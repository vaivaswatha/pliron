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

; Function to test vector forms of FPToSI, FPToUI, SIToFP and UIToFP.
define i32 @test_vector_casts() {
entry:
  %fvec0 = insertelement <2 x float> undef, float 5.000000e+00, i32 0
  %fvec1 = insertelement <2 x float> %fvec0, float 9.000000e+00, i32 1
  %fptosi = fptosi <2 x float> %fvec1 to <2 x i32>
  %fptosi_0 = extractelement <2 x i32> %fptosi, i32 0
  %fptoui = fptoui <2 x float> %fvec1 to <2 x i32>
  %fptoui_1 = extractelement <2 x i32> %fptoui, i32 1

  %ivec0 = insertelement <2 x i32> undef, i32 7, i32 0
  %ivec1 = insertelement <2 x i32> %ivec0, i32 3, i32 1
  %sitofp = sitofp <2 x i32> %ivec1 to <2 x float>
  %sitofp_0 = extractelement <2 x float> %sitofp, i32 0
  %sitofp_0_i = fptosi float %sitofp_0 to i32
  %uitofp = uitofp <2 x i32> %ivec1 to <2 x float>
  %uitofp_1 = extractelement <2 x float> %uitofp, i32 1
  %uitofp_1_i = fptosi float %uitofp_1 to i32

  %sum0 = add i32 %fptosi_0, %fptoui_1
  %sum1 = add i32 %sitofp_0_i, %uitofp_1_i
  %sum2 = add i32 %sum0, %sum1
  ret i32 %sum2
}

; Main function that calls test_casts
define i32 @main() {
entry:
  ; Example input value
  %input = add i32 0, 123456
  %scalar_result = call i32 @test_casts(i32 %input)
  %vector_result = call i32 @test_vector_casts()
  %result = add i32 %scalar_result, %vector_result
  ret i32 %result
}