import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.NullMeasurable

open Function Set Real Filter Topology TopologicalSpace MeasureTheory Metric Function

/-! # Exercises to practice -/

/- Here are a few example proofs: golf each one according to the ideas discussed in class.
Indicate which changes you made and why. -/

section example1

example {s : Set ℝ} (h : NullMeasurableSet s volume) :
    ∃ t ⊆ s, MeasurableSet t ∧ volume t = volume s ∧ volume (s \ t) = 0 := by
  have ⟨t, t_sub_s, t_m, t_eq_s⟩ := h.exists_measurable_subset_ae_eq
  use t, t_sub_s, t_m
  constructor
  · exact measure_congr t_eq_s
  · exact ae_le_set.mp t_eq_s.symm.le

-- Your version
example {s : Set ℝ} (h : NullMeasurableSet s volume) :
    ∃ t ⊆ s, MeasurableSet t ∧ volume t = volume s ∧ volume (s \ t) = 0 := by
  have ⟨t, t_sub_s, t_m, t_eq_s⟩ := h.exists_measurable_subset_ae_eq
  use t, t_sub_s, t_m
  constructor
  · exact measure_congr t_eq_s
  · exact ae_le_set.mp t_eq_s.symm.le

end example1

-- Assume this is code proposed for inclusion into your library. It is likely written in non-ideal
-- ways. For instance, it might duplicate lemmas already in mathlib (in which case, you would prefer
-- to use the existing lemmas).
section example2

-- proven above; you don't need to golf this proof
lemma nullmeasurable_measurable_null {s : Set ℝ} (h : NullMeasurableSet s volume) :
    ∃ t ⊆ s, MeasurableSet t ∧ volume t = volume s ∧ volume (s \ t) = 0 := by sorry

lemma measurable_null_nullmeasurable {s t : Set ℝ}
    (hm : NullMeasurableSet s) (hn : volume t = 0) : NullMeasurableSet (s ∪ t) :=
  NullMeasurableSet.union_null hm hn

lemma measurable_nullmeasurable {s : Set ℝ} (h : MeasurableSet s) : NullMeasurableSet s volume :=
  h.nullMeasurableSet

lemma shift_volume (s : Set ℝ) (c : ℝ) : volume ((fun x ↦ x + c) '' s) = volume s := by
  simp only [image_add_right, measure_preimage_add_right]

lemma shift_nullmeasurable {s : Set ℝ} (h : NullMeasurableSet s volume) (c : ℝ) :
    NullMeasurableSet ((fun x ↦ x + c) '' s) volume := by
  rcases nullmeasurable_measurable_null h with ⟨t, ts, tm, vs, vt⟩
  rw [← union_diff_cancel ts, image_union]
  refine measurable_null_nullmeasurable ?_ ?_
  · have : MeasurableSet ((fun x ↦ x + c) '' t) := by
      apply (MeasurableEmbedding.measurableSet_image ?_).mpr tm
      exact measurableEmbedding_addRight c
    exact measurable_nullmeasurable this
  · rw [shift_volume (s \ t), vt]

end example2

-- Your version: copy-paste the code, clean it up and say what changes you made
section example2'

-- your solution goes here

end example2'

section example3

lemma volume_mono {s t : Set ℝ} (h : s ⊆ t) : volume s ≤ volume t := by
  exact OuterMeasureClass.measure_mono volume h

lemma union_volume_null {s t : Set ℝ} (hs : MeasurableSet s) (ht : volume t = 0) :
    volume (s ∪ t) = volume s := by
  have hu : s ∪ t = s ∪ (t \ s) := union_diff_self.symm
  have hd : Disjoint s (t \ s) := disjoint_sdiff_right
  have hz : volume (t \ s) = 0 := by
    apply le_antisymm
    · rw [← ht]
      exact volume_mono diff_subset
    · exact zero_le (volume (t \ s))
  rw [hu, measure_union' hd hs, hz]
  abel

end example3

-- Your version: copy-paste the code, clean it up and say what changes you made
section example3'

-- your solution goes here

end example3'


/- Take a lemma from your formalisation project and clean up its code in the same manner. -/
-- If you like to paste its code here, you may need to add additional imports at the top,
-- and also copy any necessary auxiliary lemmas.





/-
Take a theorem from your project that is a bit slow and investigate:
* can you make a guess which tactic(s) are slow?
* can you use the profiler to investigate?
* what are possible ways to speed this up?
-/






/-! # Exercises to hand in -/

/- There are **no graded exercises** this week: work on your formalisation projects,
do the practice exercises and review the last exercises in detail. -/


/-
This exercise is a **bonus exercise**: you may gain addition points if you need them.
Take a solution of yours on an old exercise and clean it up it using your current knowledge.
Make sure to take all feedback you got into account, but also use your own judgement.
-/
