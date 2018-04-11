define i64 @function(i64 %arg) {
  %slot1 = alloca i64
  %slot2 = alloca i64
  store i64 %arg, i64* %slot1
  store i64 1, i64* %slot2
  br label %first

first:
  %val1 = load i64, i64* %slot1
  %val1gt0 = icmp sgt i64 %val1, 0
  br i1 %val1gt0, label %second, label %third

second:
  %val1a = load i64, i64* %slot1
  %val1aminus1 = add i64 %val1a, -1
  store i64 %val1aminus1, i64* %slot1
  %val2 = load i64, i64* %slot2
  %val2a = mul i64 %val2, %val1a
  store i64 %val2a, i64* %slot2
  br label %first

third:
  %val2b = load i64, i64* %slot2
  ret i64 %val2b
}
