; Based on the data flow example we did in class

define i64 @f(i64 %0) {
  %2 = alloca i64
  %3 = alloca i64
  %4 = alloca i64
  %5 = alloca i64
  store i64 %0, i64* %2
  store i64 1, i64* %3
  store i64 0, i64* %4
  store i64 0, i64* %5
  br label %6

6:
  %7 = load i64, i64* %2
  %8 = icmp sgt i64 %7, 0
  br i1 %8, label %9, label %26

9:
  %10 = load i64, i64* %3
  %11 = load i64, i64* %3
  %12 = mul i64 %10, %11
  store i64 %12, i64* %4
  %13 = load i64, i64* %3
  %14 = load i64, i64* %2
  %15 = mul i64 %13, %14
  store i64 %15, i64* %5
  %16 = load i64, i64* %2
  %17 = sub i64 %16, 1
  store i64 %17, i64* %2
  %18 = load i64, i64* %2
  %19 = and i64 %18, 1
  %20 = icmp ne i64 %19, 0
  br i1 %20, label %21, label %23

21:
  %22 = load i64, i64* %4
  store i64 %22, i64* %3
  br label %25

23:
  %24 = load i64, i64* %5
  store i64 %24, i64* %3
  br label %25

25:
  br label %6

26:
  %27 = load i64, i64* %2
  ret i64 %27
}

define i64 @main() {
  %x = call i64 @f(i64 43)
  ret i64 0
}
