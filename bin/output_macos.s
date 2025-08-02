	.section	__TEXT,__text,regular,pure_instructions
	.globl	_main
	.p2align	2
_main:
	.cfi_startproc
	stp	x29, x30, [sp, #-16]!
	mov	x29, sp
	sub	sp, sp, #144
	.cfi_def_cfa w29, 16
	.cfi_offset w30, -8
	.cfi_offset w29, -16
	mov	x0, #8
	stur	x0, [x29, #-80]
	mov	w8, #1
	stur	x8, [x29, #-8]
	fmov	d0, #1.00000000
	stur	d0, [x29, #-16]
	mov	w8, #1
	stur	w8, [x29, #-72]
	and	w8, w8, #0x1
	and	w8, w8, #0x1
	sturb	w8, [x29, #-17]
	mov	w8, #97
	sturb	w8, [x29, #-18]
	adrp	x8, l___unnamed_1@PAGE
	add	x8, x8, l___unnamed_1@PAGEOFF
	stur	x8, [x29, #-32]
	ldur	x8, [x29, #-32]
	stur	x8, [x29, #-40]
	bl	_malloc
	ldur	w8, [x29, #-72]
	ldur	x9, [x29, #-32]
	str	x9, [x0]
	stur	x0, [x29, #-48]
	mov	w9, #5
	stur	x9, [x29, #-56]
	mov	x9, #-2
	stur	x9, [x29, #-64]
	tbnz	w8, #0, LBB0_2
	b	LBB0_1
LBB0_1:
	mov	w8, #0
	stur	w8, [x29, #-84]
	b	LBB0_3
LBB0_2:
	mov	w8, #1
	stur	w8, [x29, #-84]
	b	LBB0_3
LBB0_3:
	ldur	x0, [x29, #-80]
	ldur	w8, [x29, #-84]
	mov	w9, #1
	stur	w9, [x29, #-100]
	and	w8, w8, #0x1
	and	w8, w8, w9
	sturb	w8, [x29, #-65]
	mov	w8, #1
	stur	x8, [x29, #-112]
	lsl	x8, x8, #3
	add	x8, x8, #15
	and	x9, x8, #0xfffffffffffffff0
	mov	x8, sp
	subs	x8, x8, x9
	mov	sp, x8
	stur	x8, [x29, #-120]
	bl	_malloc
	ldur	x11, [x29, #-120]
	ldur	x9, [x29, #-112]
	ldur	w8, [x29, #-100]
	mov	w10, #4
	str	x10, [x0]
	ldr	x10, [x0]
	str	x10, [x11]
	lsl	x9, x9, #3
	add	x9, x9, #15
	and	x10, x9, #0xfffffffffffffff0
	mov	x9, sp
	subs	x9, x9, x10
	mov	sp, x9
	stur	x9, [x29, #-96]
	tbnz	w8, #0, LBB0_5
	b	LBB0_6
LBB0_4:
	ldur	x9, [x29, #-96]
	ldur	x8, [x29, #-144]
	str	x8, [x9]
	mov	w8, #1
	lsl	x9, x8, #3
	add	x9, x9, #15
	and	x10, x9, #0xfffffffffffffff0
	mov	x9, sp
	subs	x9, x9, x10
	mov	sp, x9
	stur	x9, [x29, #-136]
	str	xzr, [x9]
	lsl	x8, x8, #3
	add	x8, x8, #15
	and	x9, x8, #0xfffffffffffffff0
	mov	x8, sp
	subs	x8, x8, x9
	mov	sp, x8
	stur	x8, [x29, #-128]
	str	xzr, [x8]
	b	LBB0_7
LBB0_5:
	mov	w8, #4
	stur	x8, [x29, #-144]
	b	LBB0_4
LBB0_6:
	mov	w8, #3
	stur	x8, [x29, #-144]
	b	LBB0_4
LBB0_7:
	ldur	x8, [x29, #-128]
	ldr	x8, [x8]
	subs	x8, x8, #5
	b.ge	LBB0_10
	b	LBB0_8
LBB0_8:
	ldur	x9, [x29, #-136]
	ldr	x8, [x9]
	add	x8, x8, #1
	str	x8, [x9]
	b	LBB0_9
LBB0_9:
	ldur	x9, [x29, #-128]
	ldr	x8, [x9]
	add	x8, x8, #1
	str	x8, [x9]
	b	LBB0_7
LBB0_10:
	b	LBB0_11
LBB0_11:
	ldur	x8, [x29, #-136]
	ldr	x8, [x8]
	tbz	x8, #63, LBB0_13
	b	LBB0_12
LBB0_12:
	ldur	x9, [x29, #-136]
	ldr	x8, [x9]
	subs	x8, x8, #1
	str	x8, [x9]
	b	LBB0_11
LBB0_13:
	mov	w8, #1
	lsl	x8, x8, #3
	add	x8, x8, #15
	and	x9, x8, #0xfffffffffffffff0
	mov	x8, sp
	subs	x8, x8, x9
	mov	sp, x8
	fmov	d0, #5.00000000
	str	d0, [x8]
	mov	w0, #0
	mov	sp, x29
	ldp	x29, x30, [sp], #16
	ret
	.cfi_endproc

	.section	__TEXT,__const
l___unnamed_1:
	.asciz	"f"

.subsections_via_symbols
