; switch.ll - Test switch inside a loop

define i32 @switch_in_loop(i32 %n) {
entry:
  %i = alloca i32, align 4
  %sum = alloca i32, align 4
  store i32 0, i32* %i
  store i32 0, i32* %sum
  br label %loop

loop:
  %cur = load i32, i32* %i
  %cmp = icmp slt i32 %cur, %n
  br i1 %cmp, label %body, label %exit

body:
  %val = srem i32 %cur, 4
  switch i32 %val, label %default [
    i32 0, label %case0
    i32 1, label %case1
    i32 2, label %case2
    i32 3, label %case3
  ]

case0:
  %sum0 = load i32, i32* %sum
  %add0 = add i32 %sum0, 4
  store i32 %add0, i32* %sum
  br label %inc

case1:
  %sum1 = load i32, i32* %sum
  %add1 = add i32 %sum1, 5
  store i32 %add1, i32* %sum
  br label %inc

case2:
  %sum2 = load i32, i32* %sum
  %add2 = add i32 %sum2, 6
  store i32 %add2, i32* %sum
  br label %inc

case3:
  %sum3 = load i32, i32* %sum
  %add3 = add i32 %sum3, 7
  store i32 %add3, i32* %sum
  br label %inc

default:
  br label %inc

inc:
  %cur2 = load i32, i32* %i
  %incval = add i32 %cur2, 1
  store i32 %incval, i32* %i
  br label %loop

exit:
  %result = load i32, i32* %sum
  ret i32 %result
}

define i32 @cond_switch_phi(i32 %x) {
entry:
  %cond = icmp sgt i32 %x, 1
  br i1 %cond, label %switch_block, label %neg_block

switch_block:
  switch i32 %x, label %default_block [
    i32 1, label %shared_block
    i32 2, label %case2
  ]

case2:
  %val2 = add i32 %x, 21
  br label %shared_block

default_block:
  %vald = add i32 %x, 33
  br label %shared_block

neg_block:
  %valn = sub i32 10, %x
  br label %shared_block

shared_block:
  %phi_val = phi i32 [ %x, %switch_block ], [ %val2, %case2 ], [ %vald, %default_block ], [ %valn, %neg_block ]
  ret i32 %phi_val

unreachable_block:
  unreachable
}

define i32 @main() {
entry:
  %call1 = call i32 @switch_in_loop(i32 5)
  %call2 = call i32 @switch_in_loop(i32 10)
  %call3 = call i32 @switch_in_loop(i32 7)
  %sum1 = add i32 %call1, %call2
  %sum2 = add i32 %sum1, %call3

  %call4 = call i32 @cond_switch_phi(i32 1)
  %call5 = call i32 @cond_switch_phi(i32 2)
  %call6 = call i32 @cond_switch_phi(i32 3)
  %sum3 = add i32 %call4, %call5
  %sum4 = add i32 %sum3, %call6
  ret i32 %sum4
}