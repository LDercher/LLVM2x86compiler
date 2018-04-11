define i64 @function(i64 %arg) {
  %slota = alloca i64
  %slotb = alloca i64
  store i64 %arg, i64* %slotb
  %valb = load i64, i64* %slotb
  %valble0 = icmp sle i64 %valb, 0
  br i1 %valble0, label %then, label %else

then:
  store i64 1, i64* %slota
  br label %done

else:
  %valb2 = load i64, i64* %slotb
  %valbminus1 = sub i64 %valb2, 1
  %recursive = call i64 @function(i64 %valbminus1)
  %multiplied = mul i64 %valb2, %recursive
  store i64 %multiplied, i64* %slota
  br label %done

done:
  %vala2 = load i64, i64* %slota
  ret i64 %vala2
}
