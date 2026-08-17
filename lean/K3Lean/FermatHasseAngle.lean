import K3Lean.HeckeCharacterCriterion
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

-- This is a project audit file, not a Mathlib contribution.
set_option linter.style.header false

/-!
# Replacing the angle-existence input by Hasse's bound

The former `hDeuring` argument only asserted that the Fermat-cubic trace can
be written as `2 * sqrt p * cos theta_p`, with `theta_p` in `[0, pi]`.
That assertion is an elementary consequence of Hasse's bound: define the
angle by `arccos (a_p / (2 * sqrt p))`.

The genuinely CM-specific information is therefore not this angle
parametrization.  It is the Hecke prime-character cancellation statement for
these angles.
-/

namespace K3Lean.FermatHasseAngle

open Set
open K3Lean.PublishedInputs

noncomputable section

/-- Hasse's theorem specialized to the smooth projective Fermat cubic.
The prime `3` is excluded because the cubic has bad reduction there. -/
def FermatCubicHasseBound : Prop :=
  ∀ p : Nat, Nat.Prime p → p ≠ 3 →
    |(fermatFrobeniusTrace p : Real)| ≤ 2 * Real.sqrt p

/-- The canonical Frobenius angle obtained from the normalized trace. -/
def fermatTraceAngle (p : Nat) : Real :=
  Real.arccos
    ((fermatFrobeniusTrace p : Real) / (2 * Real.sqrt p))

/-- Hasse's bound puts the normalized trace in `[-1, 1]`. -/
theorem normalizedFermatTrace_mem_Icc
    (hHasse : FermatCubicHasseBound)
    {p : Nat} (hp : Nat.Prime p) (hp3 : p ≠ 3) :
    (fermatFrobeniusTrace p : Real) / (2 * Real.sqrt p) ∈
      Set.Icc (-(1 : Real)) 1 := by
  have hpPos : (0 : Real) < p := by
    exact_mod_cast hp.pos
  have hDen : 0 < 2 * Real.sqrt p := by positivity
  have hAbs := hHasse p hp hp3
  have hBounds := abs_le.mp hAbs
  constructor
  · apply (le_div_iff₀ hDen).2
    nlinarith
  · apply (div_le_iff₀ hDen).2
    nlinarith

/-- The arccos angle lies in `[0, pi]` and recovers the Frobenius trace. -/
theorem fermatTraceAngle_data
    (hHasse : FermatCubicHasseBound)
    {p : Nat} (hp : Nat.Prime p) (hp3 : p ≠ 3) :
    fermatTraceAngle p ∈ Set.Icc (0 : Real) Real.pi ∧
      (fermatFrobeniusTrace p : Real) =
        2 * Real.sqrt p * Real.cos (fermatTraceAngle p) := by
  have hpPos : (0 : Real) < p := by
    exact_mod_cast hp.pos
  have hDen : 0 < 2 * Real.sqrt p := by positivity
  have hNorm := normalizedFermatTrace_mem_Icc hHasse hp hp3
  constructor
  · exact ⟨Real.arccos_nonneg _, Real.arccos_le_pi _⟩
  · rw [fermatTraceAngle, Real.cos_arccos hNorm.1 hNorm.2]
    field_simp [hDen.ne']

/-- The exact angle-data hypothesis used by the Hecke reduction follows from
the standard Hasse bound, with no CM theorem needed at this step. -/
theorem split_fermatTraceAngle_data
    (hHasse : FermatCubicHasseBound) :
    ∀ p : Nat, Nat.Prime p → p % 3 = 1 →
      fermatTraceAngle p ∈ Set.Icc (0 : Real) Real.pi ∧
        (fermatFrobeniusTrace p : Real) =
          2 * Real.sqrt p * Real.cos (fermatTraceAngle p) := by
  intro p hp hsplit
  apply fermatTraceAngle_data hHasse hp
  intro hp3
  subst p
  norm_num at hsplit

#check @FermatCubicHasseBound
#check @fermatTraceAngle
#check @split_fermatTraceAngle_data
#print axioms split_fermatTraceAngle_data

end

end K3Lean.FermatHasseAngle
