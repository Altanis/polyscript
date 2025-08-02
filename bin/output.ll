; ModuleID = 'a'
source_filename = "a"

@0 = private constant [2 x i8] c"f\00"

define i32 @main() {
entry:
  %0 = alloca i64, align 8
  store i64 1, ptr %0, align 4
  %1 = alloca double, align 8
  store double 1.000000e+00, ptr %1, align 8
  %2 = alloca i1, align 1
  store i1 true, ptr %2, align 1
  %3 = alloca i8, align 1
  store i8 97, ptr %3, align 1
  %4 = alloca ptr, align 8
  store ptr @0, ptr %4, align 8
  %5 = alloca ptr, align 8
  %6 = load ptr, ptr %4, align 8
  store ptr %6, ptr %5, align 8
  %7 = alloca ptr, align 8
  %8 = call ptr @malloc(i64 ptrtoint (ptr getelementptr (ptr, ptr null, i32 1) to i64))
  %9 = load ptr, ptr %4, align 8
  store ptr %9, ptr %8, align 8
  store ptr %8, ptr %7, align 8
  %10 = alloca i64, align 8
  store i64 5, ptr %10, align 4
  %11 = alloca i64, align 8
  store i64 -2, ptr %11, align 4
  %12 = alloca i1, align 1
  br i1 true, label %14, label %13

13:                                               ; preds = %entry
  br label %15

14:                                               ; preds = %entry
  br label %15

15:                                               ; preds = %14, %13
  %16 = phi i1 [ false, %13 ], [ true, %14 ]
  store i1 %16, ptr %12, align 1
  %17 = alloca i64, align 8
  %18 = call ptr @malloc(i64 ptrtoint (ptr getelementptr (i64, ptr null, i32 1) to i64))
  store i64 4, ptr %18, align 4
  %19 = load i64, ptr %18, align 4
  store i64 %19, ptr %17, align 4
  %20 = alloca i64, align 8
  br i1 true, label %25, label %26

21:                                               ; preds = %26, %25
  %22 = phi i64 [ 4, %25 ], [ 3, %26 ]
  store i64 %22, ptr %20, align 4
  %23 = alloca i64, align 8
  store i64 0, ptr %23, align 4
  %24 = alloca i64, align 8
  store i64 0, ptr %24, align 4
  br label %27

25:                                               ; preds = %15
  br label %21

26:                                               ; preds = %15
  br label %21

27:                                               ; preds = %33, %21
  %28 = load i64, ptr %24, align 4
  %29 = icmp slt i64 %28, 5
  br i1 %29, label %30, label %36

30:                                               ; preds = %27
  %31 = load i64, ptr %23, align 4
  %32 = add i64 %31, 1
  store i64 %32, ptr %23, align 4
  br label %33

33:                                               ; preds = %30
  %34 = load i64, ptr %24, align 4
  %35 = add i64 %34, 1
  store i64 %35, ptr %24, align 4
  br label %27

36:                                               ; preds = %27
  br label %37

37:                                               ; preds = %40, %36
  %38 = load i64, ptr %23, align 4
  %39 = icmp slt i64 %38, 0
  br i1 %39, label %40, label %43

40:                                               ; preds = %37
  %41 = load i64, ptr %23, align 4
  %42 = sub i64 %41, 1
  store i64 %42, ptr %23, align 4
  br label %37

43:                                               ; preds = %37
  %44 = alloca double, align 8
  store double 5.000000e+00, ptr %44, align 8
  ret i32 0
}

declare ptr @malloc(i64)
