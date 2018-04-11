define i64 @function(i64 %arg) {
  %a_cell = alloca i64
  %i_cell = alloca i64
  store i64 %arg, i64* %a_cell
  store i64 0, i64* %i_cell
  br label %for_loop

for_loop:
  %a_val1 = load i64, i64* %a_cell
  %a_gt_one = icmp sgt i64 %a_val1, 1
  br i1 %a_gt_one, label %for_body, label %for_done

for_body:
  %a_and_one = and i64 %a_val1, 1
  %a_div_two = icmp eq i64 %a_and_one, 0
  br i1 %a_div_two, label %then, label %else

then:
  %a_divided = ashr i64 %a_val1, 1
  store i64 %a_divided, i64* %a_cell
  br label %for_bottom_again

else:
  %a_multiplied = mul i64 3, %a_val1
  %a_added = add i64 %a_multiplied, 1
  store i64 %a_added, i64* %a_cell
  br label %for_bottom_again

for_bottom_again:
  %i_val = load i64, i64* %i_cell
  %i_added = add i64 %i_val, 1
  store i64 %i_added, i64* %i_cell
  br label %for_loop

for_done:
  ret i64 %i_added
}
