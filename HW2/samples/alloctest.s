	.text
	.file	"alloctest.ll"
	.globl	function
	.align	16, 0x90
	.type	function,@function
function:                               # @function
	.cfi_startproc
# BB#0:
	movq	%rdi, -8(%rsp)
	retq
.Lfunc_end0:
	.size	function, .Lfunc_end0-function
	.cfi_endproc


	.section	".note.GNU-stack","",@progbits
