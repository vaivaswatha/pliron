; LLVM IR test file: indirect_call.ll
; Uses an indirect call through a table of function pointers and returns a value from main.

@func_table = global [2 x i32 (i32)*] [i32 (i32)* @add_one, i32 (i32)* @mul_two], align 8

define i32 @add_one(i32 %x) {
entry:
  %res = add i32 %x, 1
  ret i32 %res
}

define i32 @mul_two(i32 %x) {
entry:
  %res = mul i32 %x, 2
  ret i32 %res
}

; call a function pointer taken from func_table at index %idx with argument %val
define i32 @choose_and_call(i32 %idx, i32 %val) {
entry:
  ; get pointer to table element
  %elem_ptr = getelementptr [2 x i32 (i32)*], [2 x i32 (i32)*]* @func_table, i32 0, i32 %idx
  ; load the function pointer
  %fp = load i32 (i32)*, i32 (i32)** %elem_ptr
  ; indirect call
  %out = call i32 %fp(i32 %val)
  ret i32 %out
}

define i32 @main() {
entry:
  ; calls choose_and_call with index 1 (mul_two) and argument 21 -> returns 42
  %result1 = call i32 @choose_and_call(i32 1, i32 21)
  ; calls choose_and_call with index 0 (add_one) and argument 41 -> returns 42
  %result2 = call i32 @choose_and_call(i32 0, i32 41)
  ; add the two results up
  %result = add i32 %result1, %result2
  ret i32 %result
}