; ModuleID = 'tinyml'
source_filename = "tinyml"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64"

@0 = private unnamed_addr constant [5 x i8] c"=%d\0A\00", align 1

define i32 @main() {
entry:
  %calltmp = call i32 @lambda(i32 4)
  %0 = call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([5 x i8], [5 x i8]* @0, i32 0, i32 0), i32 %calltmp)
  ret i32 0
}

define i32 @lambda(i32 %0) {
entry:
  %addtmp = add i32 %0, 1
  ret i32 %addtmp
}

; Function Attrs: nounwind
declare i32 @printf(i8* nocapture, ...) #0

attributes #0 = { nounwind }
