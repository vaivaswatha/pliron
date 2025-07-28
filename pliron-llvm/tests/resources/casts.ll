; Function to test various integer cast instructions
define i32 @test_casts(i32 %x) {
entry:
  ; Truncate i32 to i8
  %trunc = trunc i32 %x to i8
  ; Zero extend i8 to i32
  %zext = zext i8 %trunc to i32
  ; Sign extend i32 to i64
  %sext = sext i32 %zext to i64
  ; Use int to ptr cast
  %bitcast_ptr = inttoptr i64 %sext to ptr
  ; Bitcast ptr back to i64
  %bitcast_back = ptrtoint ptr %bitcast_ptr to i64
  ; Truncate i64 back to i32
  %trunc_back = trunc i64 %bitcast_back to i32
  ; Return the final truncated value
  ret i32 %trunc_back
}

; Main function that calls test_casts
define i32 @main() {
entry:
  ; Example input value
  %input = add i32 0, 123456
  %result = call i32 @test_casts(i32 %input)
  ret i32 %result
}