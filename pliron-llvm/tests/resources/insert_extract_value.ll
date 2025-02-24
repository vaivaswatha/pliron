; Define a struct type
%MyStruct = type { i32, i64 }

; Define a function to demonstrate insertvalue and extractvalue
define i32 @main() {
entry:
  ; Create an instance of the struct and insert values
  %struct = alloca %MyStruct
  %struct_init = insertvalue %MyStruct undef, i32 42, 0
  %struct_final = insertvalue %MyStruct %struct_init, i64 13, 1
  store %MyStruct %struct_final, %MyStruct* %struct

  ; Extract values from the struct
  %loaded_struct = load %MyStruct, %MyStruct* %struct
  %extracted_i32 = extractvalue %MyStruct %loaded_struct, 0
  %extracted_i64 = extractvalue %MyStruct %loaded_struct, 1

  ; Perform a simple computation on the struct elements
  %struct_computation = add i32 %extracted_i32, 1

  ; Create an array and insert values
  %array = alloca [3 x i32]
  %array_init = insertvalue [3 x i32] undef, i32 10, 0
  %array_mid = insertvalue [3 x i32] %array_init, i32 20, 1
  %array_final = insertvalue [3 x i32] %array_mid, i32 30, 2
  store [3 x i32] %array_final, [3 x i32]* %array

  ; Extract values from the array
  %loaded_array = load [3 x i32], [3 x i32]* %array
  %extracted_elem0 = extractvalue [3 x i32] %loaded_array, 0
  %extracted_elem1 = extractvalue [3 x i32] %loaded_array, 1
  %extracted_elem2 = extractvalue [3 x i32] %loaded_array, 2

  ; Perform a simple computation on the array elements
  %array_computation = add i32 %extracted_elem0, %extracted_elem1
  %final_computation = add i32 %array_computation, %extracted_elem2

  ; Combine the results of the struct and array computations
  %result = add i32 %struct_computation, %final_computation

  ret i32 %result
}
