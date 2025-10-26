; File: tests/resources/intrinsics.ll
; A small LLVM IR test that calls various math intrinsics and returns an i32
; computed from converting their results to integers.

declare float @llvm.sqrt.f32(float)
declare double @llvm.sqrt.f64(double)

declare float @llvm.pow.f32(float, float)
declare double @llvm.pow.f64(double, double)

declare float @llvm.fma.f32(float, float, float)
declare double @llvm.fma.f64(double, double, double)

declare float @llvm.sin.f32(float)
declare double @llvm.sin.f64(double)
declare float @llvm.cos.f32(float)
declare double @llvm.cos.f64(double)

declare float @llvm.exp.f32(float)
declare double @llvm.exp.f64(double)
declare float @llvm.log.f32(float)
declare double @llvm.log.f64(double)

declare float @llvm.ceil.f32(float)
declare double @llvm.ceil.f64(double)
declare float @llvm.floor.f32(float)
declare double @llvm.floor.f64(double)
declare float @llvm.trunc.f32(float)
declare double @llvm.trunc.f64(double)

declare float @llvm.fabs.f32(float)
declare double @llvm.fabs.f64(double)

declare float @llvm.copysign.f32(float, float)
declare double @llvm.copysign.f64(double, double)

define i32 @main() {
entry:
  ; sqrt tests
  %s_f32 = call float @llvm.sqrt.f32(float 4.000000e+00)
  %s_f32_i = fptosi float %s_f32 to i32

  %s_f64 = call double @llvm.sqrt.f64(double 9.000000000000000e+00)
  %s_f64_i = fptosi double %s_f64 to i32

  ; pow tests
  %p1_f32 = call float @llvm.pow.f32(float 2.000000e+00, float 3.000000e+00)
  %p1_f32_i = fptosi float %p1_f32 to i32

  %p2_f64 = call double @llvm.pow.f64(double 5.000000000000000e+00, double 2.000000000000000e+00)
  %p2_f64_i = fptosi double %p2_f64 to i32

  ; fused multiply-add tests
  %fma_f32 = call float @llvm.fma.f32(float 2.000000e+00, float 3.000000e+00, float 4.000000e+00)
  %fma_f32_i = fptosi float %fma_f32 to i32

  %fma_f64 = call double @llvm.fma.f64(double 1.500000000000000e+00, double 2.000000000000000e+00, double -1.000000000000000e+00)
  %fma_f64_i = fptosi double %fma_f64 to i32

  ; trig tests
  %sin_f32 = call float @llvm.sin.f32(float 0.000000e+00)
  %sin_f32_i = fptosi float %sin_f32 to i32

  %cos_f64 = call double @llvm.cos.f64(double 0.000000000000000e+00)
  %cos_f64_i = fptosi double %cos_f64 to i32

  ; exp/log tests
  %exp_f32 = call float @llvm.exp.f32(float 1.000000e+00)
  %exp_f32_i = fptosi float %exp_f32 to i32

  %log_f64 = call double @llvm.log.f64(double 2.71828182845904523536)
  %log_f64_i = fptosi double %log_f64 to i32

  ; rounding tests
  %ceil_f32 = call float @llvm.ceil.f32(float 1.00000e+00)
  %ceil_f32_i = fptosi float %ceil_f32 to i32

  %floor_f64 = call double @llvm.floor.f64(double 1.800000000000000e+00)
  %floor_f64_i = fptosi double %floor_f64 to i32

  %trunc_f32 = call float @llvm.trunc.f32(float 3.000000e+00)
  %trunc_f32_i = fptosi float %trunc_f32 to i32

  ; absolute / copysign tests
  %fabs_f32 = call float @llvm.fabs.f32(float -3.500000e+00)
  %fabs_f32_i = fptosi float %fabs_f32 to i32

  %copysign_f64 = call double @llvm.copysign.f64(double -2.000000000000000e+00, double 1.000000000000000e+00)
  %copysign_f64_i = fptosi double %copysign_f64 to i32

  ; accumulate results into a single integer return value
  %sum0 = add i32 0, %s_f32_i
  %sum1 = add i32 %sum0, %s_f64_i
  %sum2 = add i32 %sum1, %p1_f32_i
  %sum3 = add i32 %sum2, %p2_f64_i
  %sum4 = add i32 %sum3, %fma_f32_i
  %sum5 = add i32 %sum4, %fma_f64_i
  %sum6 = add i32 %sum5, %sin_f32_i
  %sum7 = add i32 %sum6, %cos_f64_i
  %sum8 = add i32 %sum7, %exp_f32_i
  %sum9 = add i32 %sum8, %log_f64_i
  %sum10 = add i32 %sum9, %ceil_f32_i
  %sum11 = add i32 %sum10, %floor_f64_i
  %sum12 = add i32 %sum11, %trunc_f32_i
  %sum13 = add i32 %sum12, %fabs_f32_i
  %final = add i32 %sum13, %copysign_f64_i

  ret i32 %final
}