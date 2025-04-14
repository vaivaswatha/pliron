; ModuleID = 'const_struct_array'
source_filename = "const_struct_array.ll"

define i32 @const_array() {
entry:
  ; Create a local copy of the constant array
  %array = alloca [3 x i32]
  store [3 x i32] [i32 11, i32 21, i32 31], [3 x i32]* %array

  ; Extract the elements
  %array_val = load [3 x i32], [3 x i32]* %array
  %elem0 = extractvalue [3 x i32] %array_val, 0
  %elem1 = extractvalue [3 x i32] %array_val, 1
  %elem2 = extractvalue [3 x i32] %array_val, 2

  ; Sum the elements
  %sum1 = add i32 %elem0, %elem1
  %sum2 = add i32 %sum1, %elem2

  ; Return the sum
  ret i32 %sum2
}

define i32 @const_struct() {

entry:
  ; Create a local copy of the constant struct
  %struct = alloca { i32, i32, i32 }
  store { i32, i32, i32 } { i32 10, i32 20, i32 30 }, { i32, i32, i32 }* %struct

  ; Extract the fields
  %struct_val = load { i32, i32, i32 }, { i32, i32, i32 }* %struct
  %field0 = extractvalue { i32, i32, i32 } %struct_val, 0
  %field1 = extractvalue { i32, i32, i32 } %struct_val, 1
  %field2 = extractvalue { i32, i32, i32 } %struct_val, 2

  ; Sum the fields
  %sum1 = add i32 %field0, %field1
  %sum2 = add i32 %sum1, %field2

  ; Return the sum
  ret i32 %sum2
}

define i32 @const_array_of_structs() {
entry:
  ; Create a local copy of the constant array of structs
  %array = alloca [2 x { i32, i32 }]
  store [2 x { i32, i32 }] [ { i32, i32 } { i32 1, i32 2 }, { i32, i32 } { i32 3, i32 4 } ], [2 x { i32, i32 }]* %array

  ; Extract the elements
  %array_val = load [2 x { i32, i32 }], [2 x { i32, i32 }]* %array
  %elem0 = extractvalue [2 x { i32, i32 }] %array_val, 0
  %elem1 = extractvalue [2 x { i32, i32 }] %array_val, 1

  ; Extract fields from the first struct
  %field0_0 = extractvalue { i32, i32 } %elem0, 0
  %field0_1 = extractvalue { i32, i32 } %elem0, 1

  ; Extract fields from the second struct
  %field1_0 = extractvalue { i32, i32 } %elem1, 0
  %field1_1 = extractvalue { i32, i32 } %elem1, 1

  ; Sum all the fields
  %sum1 = add i32 %field0_0, %field0_1
  %sum2 = add i32 %sum1, %field1_0
  %sum3 = add i32 %sum2, %field1_1

  ; Return the sum
  ret i32 %sum3
}

define i32 @const_struct_with_arrays() {
entry:
  ; Create a local copy of the constant struct with two array fields
  %struct = alloca { [2 x i32], [3 x i32] }
  store { [2 x i32], [3 x i32] } { [2 x i32] [i32 1, i32 2], [3 x i32] [i32 3, i32 4, i32 5] }, { [2 x i32], [3 x i32] }* %struct

  ; Extract the struct value
  %struct_val = load { [2 x i32], [3 x i32] }, { [2 x i32], [3 x i32] }* %struct

  ; Extract the first array field
  %array0 = extractvalue { [2 x i32], [3 x i32] } %struct_val, 0
  %array0_elem0 = extractvalue [2 x i32] %array0, 0
  %array0_elem1 = extractvalue [2 x i32] %array0, 1

  ; Extract the second array field
  %array1 = extractvalue { [2 x i32], [3 x i32] } %struct_val, 1
  %array1_elem0 = extractvalue [3 x i32] %array1, 0
  %array1_elem1 = extractvalue [3 x i32] %array1, 1
  %array1_elem2 = extractvalue [3 x i32] %array1, 2

  ; Sum all the elements
  %sum1 = add i32 %array0_elem0, %array0_elem1
  %sum2 = add i32 %sum1, %array1_elem0
  %sum3 = add i32 %sum2, %array1_elem1
  %sum4 = add i32 %sum3, %array1_elem2

  ; Return the sum
  ret i32 %sum4
}

define i32 @const_expr() {
entry:
  ; Return the result of the constant expression
  ret i32
    sub(
      i32 add(
        i32 ptrtoint (i32* getelementptr (i32, i32* inttoptr (i32 11 to i32*), i32 1) to i32),
        i32 ptrtoint (i32* getelementptr (i32, i32* null, i32 13) to i32)
      ),
      i32 add(
        i32 ptrtoint (i32* getelementptr (i32, i32* null, i32 1) to i32),
        i32 ptrtoint (i32* getelementptr (i32, i32* null, i32 2) to i32)
      )
    )
}

define i32 @main() {
entry:
  ; Call the const_array function
  %result1 = call i32 @const_array()

  ; Call the const_struct function
  %result2 = call i32 @const_struct()

  ; Call the const_array_of_structs function
  %result3 = call i32 @const_array_of_structs()

  ; Call the const_struct_with_arrays function
  %result4 = call i32 @const_struct_with_arrays()

  ; Call the const_expr function
  %result5 = call i32 @const_expr()

  ; Add the results to the final sum
  %temp_sum0 = add i32 %result1, %result2
  %temp_sum1 = add i32 %temp_sum0, %result3
  %temp_sum2 = add i32 %temp_sum1, %result4
  %temp_sum3 = add i32 %temp_sum2, %result5

  ; Return the final sum
  ret i32 %temp_sum3
}
