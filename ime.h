/* See LICENSE file for copyright and license details. */
#pragma once

#include "text-input-unstable-v3-protocol.h"

/* functions defined later in mew.c */
static void insert(const char *str, ssize_t n);
static void redraw(void);

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

/* buffer pixels -> surface-local coordinates */
static int
ime_surface_coord(int v)
{
	return (int)(v / scale + 0.5);
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

	sx = ime_surface_coord(ime_cursor_x);
	sy = ime_surface_coord(ime_cursor_y);
	sw = MAX(1, ime_surface_coord(ime_cursor_w));
	sh = MAX(1, ime_surface_coord(ime_cursor_h));

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

	sx = ime_surface_coord(ime_cursor_x);
	sy = ime_surface_coord(ime_cursor_y);
	sw = MAX(1, ime_surface_coord(ime_cursor_w));
	sh = MAX(1, ime_surface_coord(ime_cursor_h));

	if (sx == ime_sent_x && sy == ime_sent_y &&
	    sw == ime_sent_w && sh == ime_sent_h)
		return;

	text_input_send_cursor_rect();
}

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
	int refresh = 0;

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

	/* replace the previous preedit */
	if (preedit_text) {
		free(preedit_text);
		preedit_text = NULL;
		refresh = 1;
	}

	/* insert the commit string at the cursor */
	if (ime_commit_pending) {
		insert(ime_commit_pending, strlen(ime_commit_pending));
		free(ime_commit_pending);
		ime_commit_pending = NULL;
		refresh = 1;
	}

	/* install the new preedit, with the cursor inside it */
	if (ime_preedit_pending && ime_preedit_pending[0] != '\0') {
		preedit_text = ime_preedit_pending;
		preedit_cursor_begin = ime_preedit_begin;
		preedit_cursor_end = ime_preedit_end;
		ime_preedit_pending = NULL;
		refresh = 1;
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
ime_cleanup(void)
{
	free(preedit_text);
	preedit_text = NULL;
	free(ime_preedit_pending);
	ime_preedit_pending = NULL;
	free(ime_commit_pending);
	ime_commit_pending = NULL;

	if (text_input)
		zwp_text_input_v3_destroy(text_input);
	if (text_input_manager)
		zwp_text_input_manager_v3_destroy(text_input_manager);
	text_input = NULL;
	text_input_manager = NULL;
}
