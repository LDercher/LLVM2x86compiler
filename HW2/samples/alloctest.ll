define void @function(i64 %arg){
    %1 = alloca i64
    store i64 %arg, i64* %1
    ret void
}

