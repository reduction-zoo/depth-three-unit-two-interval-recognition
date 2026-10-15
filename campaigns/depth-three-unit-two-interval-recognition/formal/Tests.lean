import Challenge
open DepthThreeUnitTwoIntervalRecognition
example : targetWitness ⟨1,[]⟩ [(0,2)] = true := by native_decide
example : targetWitness ⟨1,[]⟩ [(0,1)] = false := by native_decide
example : targetWitness ⟨2,[(0,1)]⟩ [(0,3),(1,5)] = true := by native_decide
