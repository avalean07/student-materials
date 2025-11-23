import Mathlib.Data.List.Sort

-- Your grade for each part (homework and exam) must be at least 45.
inductive CourseResult where
  | componentTooLow
  | pass (result : Float)
  deriving Repr

-- hw_grades is the grade of each homework, between 0 and 100.
-- exam_grade is the grade for the exam, between 0 and 100
def total_grade (hw_grades : List Float) (exam_grade : Float): CourseResult :=
  let hw_grade := (hw_grades.insertionSort (fun x y => y < x) |>.take 8 |>.sum) / 8
  if hw_grade < 45 || exam_grade < 45 then .componentTooLow
  else .pass $ (hw_grade + exam_grade) / 2

-- Passing grades.
#eval total_grade [100, 100, 100, 100, 100,  100, 100, 100, 100, 100] 100
#eval total_grade [0, 100, 100, 100, 100,  100, 100, 100, 100, 100] 100
#eval total_grade [0, 0, 100, 100, 100,  100, 100, 100, 100, 100] 100
#eval total_grade [0, 0, 50, 50, 50,  50, 50, 50, 50, 50] 50
#eval total_grade [100, 100, 100, 100, 100] 50

-- Failing grades
#eval total_grade [100, 100, 100] 100
#eval total_grade [100, 100, 100, 100, 100, 100, 100, 100] 40
