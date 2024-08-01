; ModuleID = 'fib.ll'
source_filename = "fib.c"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-pc-linux-gnu"

; Function Attrs: noinline nounwind uwtable
define dso_local i32 @fib(i32 noundef %0) #0 {
  %2 = icmp sle i32 %0, 1
  br i1 %2, label %3, label %4

3:                                                ; preds = %1
  br label %15

4:                                                ; preds = %1
  %5 = icmp eq i32 %0, 2
  br i1 %5, label %6, label %7

6:                                                ; preds = %4
  br label %15

7:                                                ; preds = %4
  br label %8

8:                                                ; preds = %12, %7
  %.04 = phi i32 [ undef, %7 ], [ %11, %12 ]
  %.03 = phi i32 [ 1, %7 ], [ %11, %12 ]
  %.02 = phi i32 [ 0, %7 ], [ %.03, %12 ]
  %.01 = phi i32 [ 3, %7 ], [ %13, %12 ]
  %9 = icmp sle i32 %.01, %0
  br i1 %9, label %10, label %14

10:                                               ; preds = %8
  %11 = add nsw i32 %.03, %.02
  br label %12

12:                                               ; preds = %10
  %13 = add nsw i32 %.01, 1
  br label %8, !llvm.loop !6

14:                                               ; preds = %8
  br label %15

15:                                               ; preds = %14, %6, %3
  %.0 = phi i32 [ 0, %3 ], [ 1, %6 ], [ %.04, %14 ]
  ret i32 %.0
}

attributes #0 = { noinline nounwind uwtable "frame-pointer"="all" "min-legal-vector-width"="0" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cmov,+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }

!llvm.module.flags = !{!0, !1, !2, !3, !4}
!llvm.ident = !{!5}

!0 = !{i32 1, !"wchar_size", i32 4}
!1 = !{i32 8, !"PIC Level", i32 2}
!2 = !{i32 7, !"PIE Level", i32 2}
!3 = !{i32 7, !"uwtable", i32 2}
!4 = !{i32 7, !"frame-pointer", i32 2}
!5 = !{!"Ubuntu clang version 17.0.6 (++20231209124227+6009708b4367-1~exp1~20231209124336.77)"}
!6 = distinct !{!6, !7}
!7 = !{!"llvm.loop.mustprogress"}
