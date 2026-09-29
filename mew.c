/* See LICENSE file for copyright and license details. */
#include <errno.h>
#include <ctype.h>
#include <locale.h>
#include <poll.h>
#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <strings.h>
#include <sys/timerfd.h>
#include <wayland-client.h>
#include <xkbcommon/xkbcommon.h>

#define MAX(A, B)             ((A) > (B) ? (A) : (B))
#define MIN(A, B)             ((A) < (B) ? (A) : (B))
#define BETWEEN(X, A, B)      ((A) <= (X) && (X) <= (B))
#define LENGTH(X)             (sizeof (X) / sizeof (X)[0])

#include "drwl.h"
#include "bufpool.h"
#include "xdg-activation-v1-protocol.h"
#include "wlr-layer-shell-unstable-v1-protocol.h"
#include "text-input-unstable-v3-protocol.h"

#define TEXTW(X)              (drwl_font_getwidth(drw, (X)) + lrpad)

enum { SchemeNorm, SchemeSel, SchemeOut }; /* color schemes */

struct item {
	char *text;
	struct item *left, *right;
	int out;
};

static struct {
	struct wl_keyboard *wl_keyboard;
	struct xkb_context *xkb_context;
	struct xkb_keymap *xkb_keymap;
	struct xkb_state *xkb_state;

	struct {
		int delay;
		int period;
		int timer;
		enum wl_keyboard_key_state key_state;
		xkb_keysym_t sym;
	} repeat;

	int ctrl, shift, alt;
} kbd;

static char text[BUFSIZ] = "";
static int bh, mw, mh;
static int inputw = 0, promptw;
static int32_t scale = 1;
static int lrpad; /* sum of left and right padding */
static size_t cursor;
static struct item *items = NULL;
static struct item *matches, *matchend;
static struct item *prev, *curr, *next, *sel;
static int running = 0;

static struct wl_display *display;
static struct wl_compositor *compositor;
static struct wl_seat *seat;
static struct wl_shm *shm;
static struct wl_data_device_manager *data_device_manager;
static struct wl_data_device *data_device;
static struct wl_data_offer *data_offer;
static struct zwlr_layer_shell_v1 *layer_shell;
static struct zwlr_layer_surface_v1 *layer_surface;
static struct xdg_activation_v1 *activation;
static struct wl_surface *surface;
static struct wl_registry *registry;
static Drwl *drw;
static BufPool pool;
static struct wl_callback *frame_callback;
/* default output supplied by compositor */
static struct wl_output *output = NULL; 

/* IME (text-input-unstable-v3) */
static struct zwp_text_input_manager_v3 *text_input_manager;
static struct zwp_text_input_v3 *text_input;

/* Active preedit string (UTF-8), NULL when no preedit is active */
static char *preedit_text;
static int32_t preedit_cursor_begin;
static int32_t preedit_cursor_end;

/* Double-buffered pending IME state, applied on the next done event */
static char *ime_preedit_pending;
static int32_t ime_preedit_begin;
static int32_t ime_preedit_end;
static char *ime_commit_pending;
static uint32_t ime_serial;

/* Cursor rectangle in buffer pixels, updated by drawmenu() */
static int ime_cursor_x, ime_cursor_y, ime_cursor_w, ime_cursor_h;
/* Last cursor rectangle sent to the compositor (surface-local coords) */
static int ime_sent_x = -1, ime_sent_y, ime_sent_w, ime_sent_h;

#include "config.h"

static int (*fstrncmp)(const char *, const char *, size_t) = strncmp;
static char *(*fstrstr)(const char *, const char *) = strstr;
static int (*submit)(const char*) = puts;

static void
noop()
{
	/*
	 * meow :3c
	 */
}

static void
die(const char *fmt, ...)
{
	va_list ap;

	va_start(ap, fmt);
	vfprintf(stderr, fmt, ap);
	va_end(ap);

	if (fmt[0] && fmt[strlen(fmt)-1] == ':') {
		fputc(' ', stderr);
		perror(NULL);
	} else {
		fputc('\n', stderr);
	}

	exit(EXIT_FAILURE);
}

static void
activation_token_handle_done(void *data,
	struct xdg_activation_token_v1 *activation_token, const char *token)
{
	char *argv[] = {"/bin/sh", "-c", (char*)data, NULL};

	xdg_activation_token_v1_destroy(activation_token);

	switch (fork()) {
	case -1:
		die("fork:");
	case 0:
		setenv("XDG_ACTIVATION_TOKEN", token, 1);
		execv(argv[0], argv);
		die("execvp:");
	}

	running = 0;
}

static const struct xdg_activation_token_v1_listener activation_token_listener = {
	.done = activation_token_handle_done,
};

static int
exec_cmd(const char *text)
{
	struct xdg_activation_token_v1 *activation_token;

	activation_token = xdg_activation_v1_get_activation_token(activation);
	xdg_activation_token_v1_set_surface(activation_token, surface);
	xdg_activation_token_v1_add_listener(activation_token,
		&activation_token_listener, (void *)text);
	xdg_activation_token_v1_commit(activation_token);

	return 0;
}

static void
parse_color(uint32_t *dest, const char *src)
{
	int len;

	if (src[0] == '#')
		src++;
	len = strlen(src);
	if (len != 6 && len != 8)
		die("bad color: %s", src);

	*dest = strtoul(src, NULL, 16);
	if (len == 6)
		*dest = (*dest << 8) | 0xFF;
}

static void
loadfonts(void)
{
	char fontattrs[12];

	drwl_font_destroy(drw->font);
	snprintf(fontattrs, sizeof(fontattrs), "dpi=%d", 96 * scale);
	if (!(drwl_font_create(drw, LENGTH(fonts), fonts, fontattrs)))
		die("no fonts could be loaded");

	lrpad = drw->font->height;
	bh = drw->font->height + 2;
	lines = MAX(lines, 0);
	mh = (lines + 1) * bh;
	promptw = (prompt && *prompt) ? TEXTW(prompt) - lrpad / 4 : 0;
}

static unsigned int
textw_clamp(const char *str, unsigned int n)
{
	unsigned int w = drwl_font_getwidth_clamp(drw, str, n) + lrpad;
	return MIN(w, n);
}

static void
appenditem(struct item *item, struct item **list, struct item **last)
{
	if (*last)
		(*last)->right = item;
	else
		*list = item;

	item->left = *last;
	item->right = NULL;
	*last = item;
}

static void
calcoffsets(void)
{
	int i, n;

	if (lines > 0)
		n = lines * bh;
	else
		n = mw - (promptw + inputw + TEXTW("<") + TEXTW(">"));
	/* calculate which items will begin the next page and previous page */
	for (i = 0, next = curr; next; next = next->right)
		if ((i += (lines > 0) ? bh : textw_clamp(next->text, n)) > n)
			break;
	for (i = 0, prev = curr; prev && prev->left; prev = prev->left)
		if ((i += (lines > 0) ? bh : textw_clamp(prev->left->text, n)) > n)
			break;
}

static void
cleanup(void)
{
	size_t i;

	for (i = 0; items && items[i].text; ++i)
		free(items[i].text);
	free(items);

	free(preedit_text);
	free(ime_preedit_pending);
	free(ime_commit_pending);
	if (text_input)
		zwp_text_input_v3_destroy(text_input);
	if (text_input_manager)
		zwp_text_input_manager_v3_destroy(text_input_manager);

	bufpool_cleanup(&pool);
	drwl_setimage(drw, NULL);
	drwl_destroy(drw);
	drwl_fini();

	wl_data_device_release(data_device);
	zwlr_layer_shell_v1_destroy(layer_shell);
	xdg_activation_v1_destroy(activation);
	wl_shm_destroy(shm);
	wl_compositor_destroy(compositor);
	wl_registry_destroy(registry);
	wl_display_disconnect(display);
}

static char *
cistrstr(const char *h, const char *n)
{
	size_t i;

	if (!n[0])
		return (char *)h;

	for (; *h; ++h) {
		for (i = 0; n[i] && tolower((unsigned char)n[i]) ==
		            tolower((unsigned char)h[i]); ++i)
			;
		if (n[i] == '\0')
			return (char *)h;
	}
	return NULL;
}

static void
draw_ime_cursor(int x)
{
	int cy = (bh - drw->font->height) / 2 + 1;
	int ch = drw->font->height - 2;

	drwl_setscheme(drw, colors[SchemeNorm]);
	drwl_rect(drw, x, cy, 2, ch, 1, 0);

	ime_cursor_x = x;
	ime_cursor_y = cy;
	ime_cursor_w = 2;
	ime_cursor_h = ch;
}

/*
 * Draw the active IME preedit string at the cursor position.  All preedit
 * glyphs are underlined and a bar cursor is drawn at the byte offset given by
 * preedit_cursor_begin (-1 hides it).  Returns the new x position.
 */
static int
draw_preedit(int x, int max_x)
{
	struct fcft_font *font = drw->font;
	const int ty = (bh - font->height) / 2 + font->ascent;
	const int ul_y = ty - font->underline.position;
	const int ul_h = MAX(1, font->underline.thickness);
	enum fcft_subpixel subpixel = FCFT_SUBPIXEL_DEFAULT;
	pixman_color_t clr = convert_color(colors[SchemeNorm][ColFg]);
	pixman_image_t *fg;
	const char *p = preedit_text;
	uint32_t last_cp = 0;
	size_t byte = 0;
	int cursor_drawn = 0;

	if ((colors[SchemeNorm][ColBg] & 0xFF) != 0xFF)
		subpixel = FCFT_SUBPIXEL_NONE;

	fg = pixman_image_create_solid_fill(&clr);

	while (*p) {
		uint32_t cp = 0, state = UTF8_ACCEPT;
		const char *start = p;
		size_t cp_len;
		const struct fcft_glyph *glyph;
		long x_kern = 0;
		int pixels_needed, glyph_start_x;

		for (; *p && utf8decode(&state, &cp, *p) > UTF8_REJECT; p++)
			;
		if (!*p || state == UTF8_REJECT) {
			cp = UTF8_INVALID;
			if (p > start)
				p--;
		}
		p++;
		cp_len = p - start;

		if (preedit_cursor_begin >= 0 &&
		    (int32_t)byte == preedit_cursor_begin) {
			draw_ime_cursor(x);
			cursor_drawn = 1;
		}

		glyph = fcft_rasterize_char_utf32(font, cp, subpixel);
		if (glyph == NULL) {
			byte += cp_len;
			last_cp = 0;
			continue;
		}

		if (last_cp)
			fcft_kerning(font, last_cp, cp, &x_kern, NULL);
		x += x_kern;

		pixels_needed = MAX(glyph->x + glyph->width, glyph->advance.x);
		if (x + pixels_needed > max_x)
			break;

		glyph_start_x = x;

		if (pixman_image_get_format(glyph->pix) == PIXMAN_a8r8g8b8)
			pixman_image_composite32(PIXMAN_OP_OVER, glyph->pix, NULL,
				drw->image, 0, 0, 0, 0,
				x + glyph->x, ty - glyph->y,
				glyph->width, glyph->height);
		else
			pixman_image_composite32(PIXMAN_OP_OVER, fg, glyph->pix,
				drw->image, 0, 0, 0, 0,
				x + glyph->x, ty - glyph->y,
				glyph->width, glyph->height);

		x += glyph->advance.x;

		pixman_image_fill_rectangles(PIXMAN_OP_SRC, drw->image, &clr, 1,
			&(pixman_rectangle16_t){glyph_start_x, ul_y,
				x - glyph_start_x, ul_h});

		last_cp = cp;
		byte += cp_len;
	}

	if (preedit_cursor_begin < 0 || !cursor_drawn)
		draw_ime_cursor(x);

	pixman_image_unref(fg);
	return x;
}

static void
text_input_send_cursor_rect(void)
{
	int sx, sy, sw, sh;

	if (text_input == NULL)
		return;

	sx = ime_cursor_x / scale;
	sy = ime_cursor_y / scale;
	sw = MAX(1, ime_cursor_w / scale);
	sh = MAX(1, ime_cursor_h / scale);

	zwp_text_input_v3_set_cursor_rectangle(text_input, sx, sy, sw, sh);
	zwp_text_input_v3_commit(text_input);
	ime_serial++;
	ime_sent_x = sx;
	ime_sent_y = sy;
	ime_sent_w = sw;
	ime_sent_h = sh;
}

static void
text_input_update_cursor_rect(void)
{
	int sx, sy, sw, sh;

	if (text_input == NULL || ime_cursor_w == 0)
		return;

	sx = ime_cursor_x / scale;
	sy = ime_cursor_y / scale;
	sw = MAX(1, ime_cursor_w / scale);
	sh = MAX(1, ime_cursor_h / scale);

	if (sx == ime_sent_x && sy == ime_sent_y &&
	    sw == ime_sent_w && sh == ime_sent_h)
		return;

	text_input_send_cursor_rect();
}

static int
drawitem(struct item *item, int x, int y, int w)
{
	if (item == sel)
		drwl_setscheme(drw, colors[SchemeSel]);
	else if (item->out)
		drwl_setscheme(drw, colors[SchemeOut]);
	else
		drwl_setscheme(drw, colors[SchemeNorm]);

	return drwl_text(drw, x, y, w, bh, lrpad / 2, item->text, 0);
}

static void
drawmenu(void)
{
	unsigned int curpos;
	struct item *item;
	int x = 0, y = 0, w;
	char *censort;
	DrwBuf *buf;

	errno = 0;
	if (!(buf = bufpool_getbuf(&pool, shm, mw, mh)))
		die(errno ? "bufpool_getbuf:" : "no buffer available");
	drwl_setimage(drw, buf->image);

	drwl_setscheme(drw, colors[SchemeNorm]);
	drwl_rect(drw, 0, 0, mw, mh, 1, 1);

	if (prompt && *prompt) {
		drwl_setscheme(drw, colors[SchemeSel]);
		x = drwl_text(drw, x, 0, promptw, bh, lrpad / 2, prompt, 0);
	}
	/* draw input field */
	w = (lines > 0 || !matches) ? mw - x : inputw;
	drwl_setscheme(drw, colors[SchemeNorm]);

	if (!passwd && preedit_text && preedit_text[0] != '\0') {
		char saved = text[cursor];
		unsigned int prefix_w;
		int tx, end_x;

		/* background */
		drwl_rect(drw, x, 0, w, bh, 1, 1);

		/* text before the cursor */
		text[cursor] = '\0';
		prefix_w = drwl_font_getwidth(drw, text);
		drwl_text(drw, x, 0, w, bh, lrpad / 2, text, 0);
		text[cursor] = saved;

		tx = MIN(x + w, x + lrpad / 2 + (int)prefix_w);

		/* preedit, underlined, with the cursor inside it */
		end_x = draw_preedit(tx, x + w);

		/* text after the cursor, shifted right by the preedit */
		if (saved != '\0' && x + w - end_x > 0)
			drwl_text(drw, end_x, 0, x + w - end_x, bh, 0,
				&text[cursor], 0);
	} else {
		if (passwd) {
			censort = calloc(1, sizeof(text));
			memset(censort, '*', strlen(text));
			drwl_text(drw, x, 0, w, bh, lrpad / 2, censort, 0);
			free(censort);
		} else
			drwl_text(drw, x, 0, w, bh, lrpad / 2, text, 0);

		curpos = TEXTW(text) - TEXTW(&text[cursor]);
		if ((curpos += lrpad / 2 - 1) < w) {
			drwl_setscheme(drw, colors[SchemeNorm]);
			drwl_rect(drw, x + curpos,
				(bh - drw->font->height) / 2 + 1,
				2, drw->font->height - 2, 1, 0);
			ime_cursor_x = x + curpos;
			ime_cursor_y = (bh - drw->font->height) / 2 + 1;
			ime_cursor_w = 2;
			ime_cursor_h = drw->font->height - 2;
		} else
			ime_cursor_w = 0;
	}

	if (lines > 0) {
		/* draw vertical list */
		for (item = curr; item != next; item = item->right)
			drawitem(item, x, y += bh, mw - x);
	} else if (matches) {
		/* draw horizontal list */
		x += inputw;
		w = TEXTW("<");
		if (curr->left) {
			drwl_setscheme(drw, colors[SchemeNorm]);
			drwl_text(drw, x, 0, w, bh, lrpad / 2, "<", 0);
		}
		x += w;
		for (item = curr; item != next; item = item->right)
			x = drawitem(item, x, 0, textw_clamp(item->text, mw - x - TEXTW(">")));
		if (next) {
			w = TEXTW(">");
			drwl_setscheme(drw, colors[SchemeNorm]);
			drwl_text(drw, mw - w, 0, w, bh, lrpad / 2, ">", 0);
		}
	}

	drwl_setimage(drw, NULL);
	wl_surface_set_buffer_scale(surface, scale);
	wl_surface_attach(surface, buf->wl_buf, 0, 0);
	wl_surface_damage_buffer(surface, 0, 0, mw, mh);
	wl_surface_commit(surface);

	text_input_update_cursor_rect();
}

static void
frame_callback_handle_done(void *data, struct wl_callback *callback,
		uint32_t time)
{
	wl_callback_destroy(frame_callback);
	frame_callback = NULL;
	drawmenu();
}

static const struct wl_callback_listener frame_callback_listener = {
	.done = frame_callback_handle_done,
};

static void
redraw()
{
	if (frame_callback)
		return;
	frame_callback = wl_surface_frame(surface);
	wl_callback_add_listener(frame_callback, &frame_callback_listener, NULL);
	wl_surface_commit(surface);
}

static void
match(void)
{
	static char **tokv = NULL;
	static int tokn = 0;

	char buf[sizeof text], *s;
	int i, tokc = 0;
	size_t len, textsize;
	struct item *item, *lprefix, *lsubstr, *prefixend, *substrend;

	strcpy(buf, text);
	/* separate input text into tokens to be matched individually */
	for (s = strtok(buf, " "); s; tokv[tokc - 1] = s, s = strtok(NULL, " "))
		if (++tokc > tokn && !(tokv = realloc(tokv, ++tokn * sizeof *tokv)))
			die("cannot realloc %zu bytes:", tokn * sizeof *tokv);
	len = tokc ? strlen(tokv[0]) : 0;

	matches = lprefix = lsubstr = matchend = prefixend = substrend = NULL;
	textsize = strlen(text) + 1;
	for (item = items; item && item->text; item++) {
		for (i = 0; i < tokc; i++)
			if (!fstrstr(item->text, tokv[i]))
				break;
		if (i != tokc) /* not all tokens match */
			continue;
		/* exact matches go first, then prefixes, then substrings */
		if (!tokc || !fstrncmp(text, item->text, textsize))
			appenditem(item, &matches, &matchend);
		else if (!fstrncmp(tokv[0], item->text, len))
			appenditem(item, &lprefix, &prefixend);
		else
			appenditem(item, &lsubstr, &substrend);
	}
	if (lprefix) {
		if (matches) {
			matchend->right = lprefix;
			lprefix->left = matchend;
		} else
			matches = lprefix;
		matchend = prefixend;
	}
	if (lsubstr) {
		if (matches) {
			matchend->right = lsubstr;
			lsubstr->left = matchend;
		} else
			matches = lsubstr;
		matchend = substrend;
	}
	curr = sel = matches;
	calcoffsets();
}

static void
insert(const char *str, ssize_t n)
{
	if (strlen(text) + n > sizeof text - 1)
		return;
	/* move existing text out of the way, insert new text, and update cursor */
	memmove(&text[cursor + n], &text[cursor], sizeof text - cursor - MAX(n, 0));
	if (str)
		memcpy(&text[cursor], str, n);
	cursor += n;
	match();
}

static size_t
nextrune(int inc)
{
	ssize_t n;

	/* return location of next utf8 rune in the given direction (+1 or -1) */
	for (n = cursor + inc; n + inc >= 0 && (text[n] & 0xc0) == 0x80; n += inc)
		;
	return n;
}

static void
movewordedge(int dir)
{
	if (dir < 0) { /* move cursor to the start of the word*/
		while (cursor > 0 && strchr(worddelimiters, text[nextrune(-1)]))
			cursor = nextrune(-1);
		while (cursor > 0 && !strchr(worddelimiters, text[nextrune(-1)]))
			cursor = nextrune(-1);
	} else { /* move cursor to the end of the word */
		while (text[cursor] && strchr(worddelimiters, text[cursor]))
			cursor = nextrune(+1);
		while (text[cursor] && !strchr(worddelimiters, text[cursor]))
			cursor = nextrune(+1);
	}
}

static void
paste(void)
{
	int fds[2];
	ssize_t n;
	char buf[1024];

	if (!data_offer)
		return;

	if (pipe(fds) < 0)
		die("pipe");

	wl_data_offer_receive(data_offer, "text/plain", fds[1]);
	close(fds[1]);

	wl_display_roundtrip(display);

	for (;;) {
		n = read(fds[0], buf, sizeof(buf));
		if (n <= 0)
			break;
		insert(buf, n);
	}
	close(fds[0]);

	wl_data_offer_destroy(data_offer);
	data_offer = NULL;
}

static void
keyboard_keypress(enum wl_keyboard_key_state state, xkb_keysym_t sym)
{
	char buf[8];

	if (state != WL_KEYBOARD_KEY_STATE_PRESSED)
		return;

	if (kbd.ctrl) {
		switch (xkb_keysym_to_lower(sym)) {
		case XKB_KEY_a: sym = XKB_KEY_Home; break;
		case XKB_KEY_b: sym = XKB_KEY_Left; break;
		case XKB_KEY_c: sym = XKB_KEY_Escape; break;
		case XKB_KEY_d: sym = XKB_KEY_Delete; break;
		case XKB_KEY_e: sym = XKB_KEY_End; break;
		case XKB_KEY_f: sym = XKB_KEY_BackSpace; break;
		case XKB_KEY_g: sym = XKB_KEY_Escape; break;
		case XKB_KEY_h: sym = XKB_KEY_BackSpace; break;
		case XKB_KEY_i: sym = XKB_KEY_Tab; break;
		case XKB_KEY_j: /* fallthrough */
		case XKB_KEY_J: /* fallthrough */
		case XKB_KEY_m: /* fallthrough */
		case XKB_KEY_M: sym = XKB_KEY_Return; break;
		case XKB_KEY_n: sym = XKB_KEY_Down; break;
		case XKB_KEY_p: sym = XKB_KEY_Up; break;

		case XKB_KEY_k: /* delete right */
			text[cursor] = '\0';
			match();
			goto draw;
		case XKB_KEY_u: /* delete left */
			insert(NULL, 0 - cursor);
			goto draw;
		case XKB_KEY_w: /* delete word */
			while (cursor > 0 && strchr(worddelimiters, text[nextrune(-1)]))
				insert(NULL, nextrune(-1) - cursor);
			while (cursor > 0 && !strchr(worddelimiters, text[nextrune(-1)]))
				insert(NULL, nextrune(-1) - cursor);
			goto draw;
		case XKB_KEY_y: /* paste selection */
		case XKB_KEY_Y:
			paste();
			goto draw;
		case XKB_KEY_Left:
		case XKB_KEY_KP_Left:
			movewordedge(-1);
			goto draw;
		case XKB_KEY_Right:
		case XKB_KEY_KP_Right:
			movewordedge(+1);
			goto draw;
		case XKB_KEY_Return:
		case XKB_KEY_KP_Enter:
			break;
		case XKB_KEY_bracketleft:
			cleanup();
			exit(EXIT_FAILURE);
		default:
			return;
		}
	} else if (kbd.alt) {
		switch(sym) {
		case XKB_KEY_b:
			movewordedge(-1);
			goto draw;
		case XKB_KEY_f:
			movewordedge(+1);
			goto draw;
		case XKB_KEY_g: sym = XKB_KEY_Home;  break;
		case XKB_KEY_G: sym = XKB_KEY_End;   break;
		case XKB_KEY_h: sym = XKB_KEY_Up;    break;
		case XKB_KEY_j: sym = XKB_KEY_Next;  break;
		case XKB_KEY_k: sym = XKB_KEY_Prior; break;
		case XKB_KEY_l: sym = XKB_KEY_Down;  break;
		default:
			return;
		}
	}

	switch (sym) {
	case XKB_KEY_Delete:
	case XKB_KEY_KP_Delete:
		if (text[cursor] == '\0')
			return;
		cursor = nextrune(+1);
		/* fallthrough */
	case XKB_KEY_BackSpace:
		if (cursor == 0)
			return;
		insert(NULL, nextrune(-1) - cursor);
		break;
	case XKB_KEY_End:
	case XKB_KEY_KP_End:
		if (text[cursor] != '\0') {
			cursor = strlen(text);
			break;
		}
		if (next) {
			/* jump to end of list and position items in reverse */
			curr = matchend;
			calcoffsets();
			curr = prev;
			calcoffsets();
			while (next && (curr = curr->right))
				calcoffsets();
		}
		sel = matchend;
		break;
	case XKB_KEY_Escape:
		cleanup();
		exit(EXIT_FAILURE);
	case XKB_KEY_Home:
	case XKB_KEY_KP_Home:
		if (sel == matches) {
			cursor = 0;
			break;
		}
		sel = curr = matches;
		calcoffsets();
		break;
	case XKB_KEY_Left:
	case XKB_KEY_KP_Left:
		if (cursor > 0 && (!sel || !sel->left || lines > 0)) {
			cursor = nextrune(-1);
			break;
		}
		if (lines > 0)
			return;
		/* fallthrough */
	case XKB_KEY_Up:
	case XKB_KEY_KP_Up:
		if (sel && sel->left && (sel = sel->left)->right == curr) {
			curr = prev;
			calcoffsets();
		}
		break;
	case XKB_KEY_Next:
	case XKB_KEY_KP_Next:
		if (!next)
			return;
		sel = curr = next;
		calcoffsets();
		break;
	case XKB_KEY_Prior:
	case XKB_KEY_KP_Prior:
		if (!prev)
			return;
		sel = curr = prev;
		calcoffsets();
		break;
	case XKB_KEY_Return:
	case XKB_KEY_KP_Enter:
		submit((sel && !kbd.shift) ? sel->text : text);
		if (!kbd.ctrl && submit != exec_cmd) {
			running = 0;
			return;
		}
		if (sel)
			sel->out = 1;
		break;
	case XKB_KEY_Right:
	case XKB_KEY_KP_Right:
		if (text[cursor] != '\0') {
			cursor = nextrune(+1);
			break;
		}
		if (lines > 0)
			return;
		/* fallthrough */
	case XKB_KEY_Down:
	case XKB_KEY_KP_Down:
		if (sel && sel->right && (sel = sel->right) == next) {
			curr = next;
			calcoffsets();
		}
		break;
	case XKB_KEY_Tab:
		if (!sel)
			return;
		cursor = strnlen(sel->text, sizeof text - 1);
		memcpy(text, sel->text, cursor);
		text[cursor] = '\0';
		match();
		break;
	default:
		if (xkb_keysym_to_utf8(sym, buf, 8))
			insert(buf, strnlen(buf, 8));
	}
draw:
	redraw();
}

static void
keyboard_handle_keymap(void *data, struct wl_keyboard *wl_keyboard,
		uint32_t format, int32_t fd, uint32_t size)
{
	char *map_shm;
	struct xkb_keymap *new_keymap;

	if (format != WL_KEYBOARD_KEYMAP_FORMAT_XKB_V1)
		die("unknown keymap");

	map_shm = mmap(NULL, size, PROT_READ, MAP_SHARED, fd, 0);
	if (map_shm == MAP_FAILED)
		die("mmap:");

	new_keymap = xkb_keymap_new_from_string(kbd.xkb_context, map_shm,
		XKB_KEYMAP_FORMAT_TEXT_V1, XKB_KEYMAP_COMPILE_NO_FLAGS);
	munmap(map_shm, size);
	close(fd);

	if (!new_keymap)
		return;

	if (kbd.xkb_state)
		xkb_state_unref(kbd.xkb_state);
	if (kbd.xkb_keymap)
		xkb_keymap_unref(kbd.xkb_keymap);
	kbd.xkb_keymap = new_keymap;
	kbd.xkb_state = xkb_state_new(kbd.xkb_keymap);
}

static void
keyboard_handle_leave(void *data, struct wl_keyboard *wl_keyboard,
		uint32_t serial, struct wl_surface *surface)
{
	/*
	 * In dmenu(1), if the keyboard cannot be grabbed, it will
	 * immediately exit. This is done before dmenu is initialized,
	 * but can't be the same for Wayland. If a new layer surface
	 * wants keyboard, it will get keyboard, set_exclusivity doesn't
	 * seem to work.
	 */
	 die("lost keyboard");
}

static void
keyboard_handle_key(void *data, struct wl_keyboard *wl_keyboard,
		uint32_t serial, uint32_t time, uint32_t key, uint32_t _key_state)
{
	struct itimerspec spec = { 0 };
	enum wl_keyboard_key_state key_state = _key_state;
	xkb_keysym_t sym;

	if (!kbd.xkb_state)
		return;
	sym = xkb_state_key_get_one_sym(kbd.xkb_state, key + 8);


	keyboard_keypress(key_state, sym);

	if (key_state == WL_KEYBOARD_KEY_STATE_PRESSED && kbd.repeat.period >= 0) {
		kbd.repeat.key_state = key_state;
		kbd.repeat.sym = sym;
		spec.it_value.tv_sec = kbd.repeat.delay / 1000;
		spec.it_value.tv_nsec = (kbd.repeat.delay % 1000) * 1000000l;
	}
	timerfd_settime(kbd.repeat.timer, 0, &spec, NULL);
}

static void
keyboard_handle_modifiers(void *data, struct wl_keyboard *wl_keyboard,
		uint32_t serial, uint32_t mods_depressed,
		uint32_t mods_latched, uint32_t mods_locked, uint32_t group)
{
	if (!kbd.xkb_state)
		return;
	xkb_state_update_mask(kbd.xkb_state,
		mods_depressed, mods_latched, mods_locked, 0, 0, group);
	kbd.ctrl = xkb_state_mod_name_is_active(kbd.xkb_state,
		XKB_MOD_NAME_CTRL,
		XKB_STATE_MODS_DEPRESSED | XKB_STATE_MODS_LATCHED);
	kbd.shift = xkb_state_mod_name_is_active(kbd.xkb_state,
		XKB_MOD_NAME_SHIFT,
		XKB_STATE_MODS_DEPRESSED | XKB_STATE_MODS_LATCHED);
	kbd.alt = xkb_state_mod_name_is_active(kbd.xkb_state,
		XKB_MOD_NAME_ALT,
		XKB_STATE_MODS_DEPRESSED | XKB_STATE_MODS_LATCHED);
}

static void
keyboard_repeat(void)
{
	struct itimerspec spec = { 0 };

	keyboard_keypress(kbd.repeat.key_state, kbd.repeat.sym);

	spec.it_value.tv_sec = kbd.repeat.period / 1000;
	spec.it_value.tv_nsec = (kbd.repeat.period % 1000) * 1000000l;
	timerfd_settime(kbd.repeat.timer, 0, &spec, NULL);
}

static void
keyboard_handle_repeat_info(void *data, struct wl_keyboard *wl_keyboard,
		int32_t rate, int32_t delay)
{
	kbd.repeat.delay = delay;
	kbd.repeat.period = rate >= 0 ? 1000 / rate : -1;
}

static const struct wl_keyboard_listener keyboard_listener = {
	.keymap = keyboard_handle_keymap,
	.enter = noop,
	.leave = keyboard_handle_leave,
	.key = keyboard_handle_key,
	.modifiers = keyboard_handle_modifiers,
	.repeat_info = keyboard_handle_repeat_info,
};

/*---------------------------------------------------------------------------
 * text-input-unstable-v3
 *---------------------------------------------------------------------------*/

static void
text_input_handle_enter(void *data, struct zwp_text_input_v3 *ti,
		struct wl_surface *surface)
{
	free(ime_preedit_pending);
	ime_preedit_pending = NULL;
	free(ime_commit_pending);
	ime_commit_pending = NULL;

	zwp_text_input_v3_enable(ti);
	zwp_text_input_v3_set_content_type(ti,
		ZWP_TEXT_INPUT_V3_CONTENT_HINT_NONE,
		ZWP_TEXT_INPUT_V3_CONTENT_PURPOSE_NORMAL);

	/* enable + content type must be committed; also report the cursor */
	text_input_send_cursor_rect();
}

static void
text_input_handle_leave(void *data, struct zwp_text_input_v3 *ti,
		struct wl_surface *surface)
{
	free(ime_preedit_pending);
	ime_preedit_pending = NULL;
	free(ime_commit_pending);
	ime_commit_pending = NULL;

	if (preedit_text) {
		free(preedit_text);
		preedit_text = NULL;
		redraw();
	}

	zwp_text_input_v3_disable(ti);
	zwp_text_input_v3_commit(ti);
	ime_serial++;
}

static void
text_input_handle_preedit_string(void *data, struct zwp_text_input_v3 *ti,
		const char *text, int32_t cursor_begin, int32_t cursor_end)
{
	free(ime_preedit_pending);
	ime_preedit_pending = text ? strdup(text) : NULL;
	ime_preedit_begin = cursor_begin;
	ime_preedit_end = cursor_end;
}

static void
text_input_handle_commit_string(void *data, struct zwp_text_input_v3 *ti,
		const char *text)
{
	free(ime_commit_pending);
	ime_commit_pending = text ? strdup(text) : NULL;
}

static void
text_input_handle_delete_surrounding_text(void *data,
		struct zwp_text_input_v3 *ti,
		uint32_t before_length, uint32_t after_length)
{
	/* We never set surrounding text, so nothing to delete */
}

static void
text_input_handle_done(void *data, struct zwp_text_input_v3 *ti,
		uint32_t serial)
{
	bool refresh = false;

	/*
	 * The serial echoes the number of commit() requests we have made.
	 * Discard stale events.
	 */
	if (serial != ime_serial) {
		free(ime_preedit_pending);
		ime_preedit_pending = NULL;
		free(ime_commit_pending);
		ime_commit_pending = NULL;
		return;
	}

	/* 1. Replace existing preedit */
	if (preedit_text) {
		free(preedit_text);
		preedit_text = NULL;
		refresh = true;
	}

	/* 3. Insert commit string at the cursor */
	if (ime_commit_pending) {
		insert(ime_commit_pending, strlen(ime_commit_pending));
		free(ime_commit_pending);
		ime_commit_pending = NULL;
		refresh = true;
	}

	/* 5 & 6. Insert new preedit, place cursor inside it */
	if (ime_preedit_pending && ime_preedit_pending[0] != '\0') {
		preedit_text = ime_preedit_pending;
		preedit_cursor_begin = ime_preedit_begin;
		preedit_cursor_end = ime_preedit_end;
		ime_preedit_pending = NULL;
		refresh = true;
	} else {
		free(ime_preedit_pending);
		ime_preedit_pending = NULL;
	}

	if (refresh)
		redraw();
}

static const struct zwp_text_input_v3_listener text_input_listener = {
	.enter = text_input_handle_enter,
	.leave = text_input_handle_leave,
	.preedit_string = text_input_handle_preedit_string,
	.commit_string = text_input_handle_commit_string,
	.delete_surrounding_text = text_input_handle_delete_surrounding_text,
	.done = text_input_handle_done,
};

static void
text_input_create(void)
{
	if (text_input_manager == NULL || seat == NULL || text_input != NULL)
		return;

	text_input = zwp_text_input_manager_v3_get_text_input(
		text_input_manager, seat);
	if (text_input == NULL)
		return;

	zwp_text_input_v3_add_listener(text_input, &text_input_listener, NULL);
}

static void
layer_surface_handle_configure(void *data, struct zwlr_layer_surface_v1 *layer_surface,
		uint32_t serial, uint32_t width, uint32_t height)
{
	if (mw / scale == width && mh / scale == height)
		return;

	mw = width * scale;
	mh = height * scale;
	inputw = mw / 3; /* input width: ~33% of output width */
	match();
	zwlr_layer_surface_v1_ack_configure(layer_surface, serial);
	drawmenu();
}

static void
layer_surface_handle_closed(void *data, struct zwlr_layer_surface_v1 *surface)
{
	running = 0;
}

static const struct zwlr_layer_surface_v1_listener layer_surface_listener = {
	.configure = layer_surface_handle_configure,
	.closed = layer_surface_handle_closed,
};

static void 
surface_handle_preferred_scale(void *data,
	struct wl_surface *wl_surface, int32_t factor)
{
	if (scale == factor)
		return;
	scale = factor;
	loadfonts();

	/* the scale of the surface is only known after an initial draw, not before :( */
	zwlr_layer_surface_v1_set_size(layer_surface, 0, mh / scale);
	redraw();
}

static const struct wl_surface_listener surface_listener = {
	.enter = noop,
	.leave = noop,
	.preferred_buffer_scale = surface_handle_preferred_scale,
	.preferred_buffer_transform = noop,
};

static void
data_device_handle_selection(void *data, struct wl_data_device *data_device,
		struct wl_data_offer *_data_offer)
{
	if (data_offer)
		wl_data_offer_destroy(data_offer);

	data_offer = _data_offer;
}

static const struct wl_data_device_listener data_device_listener = {
	.data_offer = noop,
	.selection = data_device_handle_selection,
};

static void
output_handle_name(void *data, struct wl_output *wl_output, const char *name)
{
	if (output_name && !strcmp(name, output_name))
		output = wl_output;
	else
		wl_output_destroy(wl_output);
}

static const struct wl_output_listener output_listener = {
	.geometry = noop,
	.mode = noop,
	.done = noop,
	.scale = noop,
	.name = output_handle_name,
	.description = noop,
};

static void
seat_handle_capabilities(void *data, struct wl_seat *wl_seat, enum wl_seat_capability caps)
{
	if (!(caps & WL_SEAT_CAPABILITY_KEYBOARD))
		return;

	kbd.wl_keyboard = wl_seat_get_keyboard(seat);
	if (!(kbd.xkb_context = xkb_context_new(XKB_CONTEXT_NO_FLAGS)))
		die("xkb_context_new failed");
	if ((kbd.repeat.timer = timerfd_create(CLOCK_MONOTONIC, 0)) < 0)
		die("timerfd_create:");
	wl_keyboard_add_listener(kbd.wl_keyboard, &keyboard_listener, NULL);

	text_input_create();
}

static const struct wl_seat_listener seat_listener = {
	.capabilities = seat_handle_capabilities,
	.name = noop,
};

static void
registry_handle_global(void *data, struct wl_registry *registry,
		uint32_t name, const char *interface, uint32_t version)
{
	if (!strcmp(interface, wl_compositor_interface.name))
		compositor = wl_registry_bind(registry, name, &wl_compositor_interface, 6);
 	else if (!strcmp(interface, wl_shm_interface.name))
		shm = wl_registry_bind(registry, name, &wl_shm_interface, 1);
	else if (!strcmp(interface, zwlr_layer_shell_v1_interface.name))
		layer_shell = wl_registry_bind(registry, name,
			&zwlr_layer_shell_v1_interface, 1);
	else if (!strcmp(interface, wl_data_device_manager_interface.name))
		data_device_manager = wl_registry_bind(registry, name,
			&wl_data_device_manager_interface, 3);
	else if (!strcmp(interface, xdg_activation_v1_interface.name))
		activation = wl_registry_bind(registry, name, &xdg_activation_v1_interface, 1);
	else if (!strcmp(interface, wl_output_interface.name)) {
		struct wl_output *output = wl_registry_bind(registry, name,
			&wl_output_interface, 4);
		wl_output_add_listener(output, &output_listener, NULL);
	} else if (!strcmp(interface, wl_seat_interface.name)) {
		seat = wl_registry_bind (registry, name, &wl_seat_interface, 4);
		wl_seat_add_listener(seat, &seat_listener, NULL);
	} else if (!strcmp(interface, zwp_text_input_manager_v3_interface.name)) {
		text_input_manager = wl_registry_bind(registry, name,
			&zwp_text_input_manager_v3_interface, 1);
		text_input_create();
	}
}

static const struct wl_registry_listener registry_listener = {
	.global = registry_handle_global,
	.global_remove = noop,
};

static void
readstdin(void)
{
	char *line = NULL;
	size_t i, itemsiz = 0, linesiz = 0;
	ssize_t len;

	if (passwd) {
		inputw = lines = 0;
		return;
	}

	/* read each line from stdin and add it to the item list */
	for (i = 0; (len = getline(&line, &linesiz, stdin)) != -1; i++) {
		if (i + 1 >= itemsiz) {
			itemsiz += 256;
			if (!(items = realloc(items, itemsiz * sizeof(*items))))
				die("cannot realloc %zu bytes:", itemsiz * sizeof(*items));
		}
		if (line[len - 1] == '\n')
			line[len - 1] = '\0';
		if (!(items[i].text = strdup(line)))
			die("strdup:");

		items[i].out = 0;
	}
	free(line);
	if (items)
		items[i].text = NULL;
	lines = MIN(lines, i);
}

static void
run(void)
{
	struct pollfd pfds[] = { 
		{ wl_display_get_fd(display), POLLIN },
		{ kbd.repeat.timer, POLLIN },
	}; 

	running = 1;
	while (running) { 
		wl_display_flush(display);

		if (poll(pfds, LENGTH(pfds), -1) < 0)
			die("poll:");

		if (pfds[0].revents & POLLIN)
			if (wl_display_dispatch(display) < 0)
				die("display dispatch failed");

		if (pfds[1].revents & POLLIN)
			keyboard_repeat();
	}
}

static void
setup(void)
{
	if (!(display = wl_display_connect(NULL)))
		die("failed to connect to wayland");

	registry = wl_display_get_registry(display);
	wl_registry_add_listener(registry, &registry_listener, NULL);
	wl_display_roundtrip(display);
	wl_display_roundtrip(display); /* output & seat listeners */
	
	if (!compositor)
		die("wl_compositor not available");
	if (!shm)
		die("wl_shm not available");
	if (!layer_shell)
		die("layer_shell not available");
	if (!data_device_manager)
		die("data_device_manager not available");

	if (output_name && !output)
		die("output %s not found", output_name);

	data_device = wl_data_device_manager_get_data_device(
		data_device_manager, seat);
	wl_data_device_add_listener(data_device, &data_device_listener, NULL);

	drwl_init();
	if (!(drw = drwl_create()))
		die("cannot create drwl drawing context");
	loadfonts();

	surface = wl_compositor_create_surface(compositor);
	wl_surface_add_listener(surface, &surface_listener, NULL);

	layer_surface = zwlr_layer_shell_v1_get_layer_surface(layer_shell,
				surface, output, ZWLR_LAYER_SHELL_V1_LAYER_OVERLAY, "mew");
	zwlr_layer_surface_v1_set_size(layer_surface, 0, mh);
	zwlr_layer_surface_v1_set_anchor(layer_surface, 
		(top ? ZWLR_LAYER_SURFACE_V1_ANCHOR_TOP : ZWLR_LAYER_SURFACE_V1_ANCHOR_BOTTOM ) |
		ZWLR_LAYER_SURFACE_V1_ANCHOR_LEFT | ZWLR_LAYER_SURFACE_V1_ANCHOR_RIGHT);
	zwlr_layer_surface_v1_set_exclusive_zone(layer_surface, -1);
	zwlr_layer_surface_v1_set_keyboard_interactivity(layer_surface, 1);
	zwlr_layer_surface_v1_add_listener(layer_surface, &layer_surface_listener, NULL);

	wl_surface_commit(surface);
}

static void
usage(void)
{
	die("usage: mew [-beivP] [-l lines] [-p prompt] [-f font] [-o output]\n"
	    "           [-nb color] [-nf color] [-sb color] [-sf color]");
}

int
main(int argc, char *argv[])
{
	int i;

	for (i = 1; i < argc; i++) {
		/* these options take no arguments */
		if (!strcmp(argv[i], "-v")) {
			puts("mew-"VERSION);
			exit(0);
		} else if (!strcmp(argv[i], "-b"))
			top = 0;
		else if (!strcmp(argv[i], "-e"))
			submit = exec_cmd;
		else if (!strcmp(argv[i], "-i")) { 
			fstrncmp = strncasecmp;
			fstrstr = cistrstr;
		} else if (!strcmp(argv[i], "-P"))
			passwd = 1;
		else if (i + 1 == argc)
			usage();
		else if (!strcmp(argv[i], "-l"))
			lines = atoi(argv[++i]);
		else if (!strcmp(argv[i], "-o"))
			output_name = argv[++i];
		else if (!strcmp(argv[i], "-p"))
			prompt = argv[++i];
		else if (!strcmp(argv[i], "-f"))
			fonts[0] = argv[++i];
		else if (!strcmp(argv[i], "-nb"))
			parse_color(&colors[SchemeNorm][ColBg], argv[++i]);
		else if (!strcmp(argv[i], "-nf"))
			parse_color(&colors[SchemeNorm][ColFg], argv[++i]);
		else if (!strcmp(argv[i], "-sb"))
			parse_color(&colors[SchemeSel][ColBg], argv[++i]);
		else if (!strcmp(argv[i], "-sf"))
			parse_color(&colors[SchemeSel][ColFg], argv[++i]);
		else
			usage();
	}

	readstdin();
#ifdef __OpenBSD__
	if (pledge("stdio rpath", NULL) == -1)
		die("pledge");
#endif
	setup();
	run();
	cleanup();

	return EXIT_SUCCESS;
}
