module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.GlobalRationalGL.BridgeEx
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle330
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.GlobalRationalGL.IntegralConjugation.IntsOv
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.GlobalRationalGL.IntegralConjugation.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.GlobalRationalGL.IntegralConjugation.ExistsUnitNormQuotientLift
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.GlobalRationalGL.IntegralConjugation.Bundle002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.GlobalRationalGL.IntegralConjugation.Bundle003
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.Valuation.LocalSubring
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil Formalism.BasicNotions Matrix
open UpperTheory.V UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict UpperTheory.V.Z.Sym.Dict.Br UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob
open UpperTheory.V.W (Plc Lp)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem mem_KGL_iff {L : Type} [Field L] [NumberField L] [IsCMField L] (w : Plc L) {n : ℕ}
    (x : GL (Fin n) (Kw w)) : x ∈ GlobalTheory.LFun.KGL w (n := n) ↔
      (∀ i j, (x : Matrix (Fin n) (Fin n) (Kw w)) i j ∈ w.adicCompletionIntegers L) ∧
      ∀ i j, ((x⁻¹ : GL (Fin n) (Kw w)) : Matrix (Fin n) (Fin n) (Kw w)) i j ∈ w.adicCompletionIntegers L := by
  rw [← GlobalTheory.HeckeEigConj.KO_eq_KGL, GlobalTheory.SplitFlip.mem_KO_iff]
  have h : ∀ y : Kw w, y ∈ 𝒪[Kw w] ↔ y ∈ w.adicCompletionIntegers L := fun y => ((intsOv L w).2 y).symm
  simp only [h]

theorem UpperTheory.V.Z.Sym.Dict.Br.okG :
    ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (B : Bridge L), (∀ (g : GA B.Δ) v, g.1 v ∈ KU (Ov v) _ ↔ ∀ w, un w = v → cLoc w (B.bG g : UA L 3) ∈ GlobalTheory.LFun.KGL w (n := 3)) ∧ (∀ (g : GA B.Δ) v, g.1 v = 1 ↔ ∀ w, un w = v → cLoc w (B.bG g : UA L 3) = 1) ∧ ∀ w (S : B.toRingBr.Split w) (g : GA B.Δ), cLoc w (B.bG g : UA L 3) = GeneralLinearGroup.map (S.i : Kv (un w) →+* Kw w) (Sig.eU S.hs (g.1 (un w))) := by
  intro L _ _ _ B
  have hm : ∀ (g : GA B.Δ) (w : Plc L) (i j : Fin 3),
      (cLoc w (B.bG g : UA L 3) : Matrix (Fin 3) (Fin 3) (Kw w)) i j
        = B.ρ _ w rfl ((g.1 (un w) : Matrix (Fin 3) (Fin 3) _) i j) :=
    fun g w i j => congrFun (congrFun (B.bG_loc g w) i) j
  have hi : ∀ (g : GA B.Δ) (w : Plc L) (i j : Fin 3),
      (((cLoc w (B.bG g : UA L 3))⁻¹ : GL (Fin 3) (Kw w)) : Matrix (Fin 3) (Fin 3) (Kw w)) i j
        = B.ρ _ w rfl (star ((g.1 (un w) : Matrix (Fin 3) (Fin 3) _) j i)) := by
    intro g w i j
    have h := hm g⁻¹ w i j
    rw [B.bG.map_inv, InvMemClass.coe_inv, map_inv] at h
    exact h
  refine ⟨fun g v => ?_, fun g v => ?_, fun w S g => ?_⟩
  · constructor
    · intro hK w h
      subst h
      rw [mem_KGL_iff]
      refine ⟨fun i j => ?_, fun i j => ?_⟩
      · rw [hm]
        exact (B.ρ_int _ _).1 (hK i j).1 w rfl
      · rw [hi]
        exact (B.ρ_int _ _).1 (hK j i).2 w rfl
    · intro H i j
      refine ⟨(B.ρ_int _ _).2 fun w h => ?_, (B.ρ_int _ _).2 fun w h => ?_⟩
      · subst h
        have := ((mem_KGL_iff _ _).1 (H w rfl)).1 i j
        rwa [hm] at this
      · subst h
        have := ((mem_KGL_iff _ _).1 (H w rfl)).2 j i
        rwa [hi] at this
  · constructor
    · intro h1 w h
      subst h
      apply Units.ext
      have := B.bG_loc g w
      rw [h1] at this
      refine this.trans ?_
      exact Matrix.map_one _ (map_zero _) (map_one _)
    · intro H
      apply Subtype.ext
      refine Matrix.ext fun i j => ?_
      apply sub_eq_zero.1
      apply B.ρ_inj
      intro w h
      cases h
      have e2 := hm g w i j
      rw [H w rfl, Units.val_one] at e2
      have e3 : B.ρ _ w rfl ((1 : Matrix (Fin 3) (Fin 3) (Lsq (Kv (un w)) (cv (un w) B.Δ))) i j) = (1 : Matrix (Fin 3) (Fin 3) (Kw w)) i j :=
        congrFun (congrFun (Matrix.map_one (B.ρ _ w rfl) (map_zero _) (map_one _)) i) j
      rw [map_sub, ← e2]
      exact sub_eq_zero.2 e3.symm
  · apply Units.ext
    refine (B.bG_loc g w).trans ?_
    refine Matrix.ext fun i j => ?_
    exact S.ρ_eq _
end

section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil Formalism.BasicNotions Matrix
open UpperTheory.V UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict UpperTheory.V.Z.Sym.Dict.Br UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob
open UpperTheory.V.W (Plc Lp)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Z.Sym.Dict.Br

variable {L : Type} [Field L] [NumberField L] [IsCMField L]

private theorem ad_ext {a b : Ad L} (hi : pInf L a = pInf L b)
    (hf : ∀ w : Plc L, pLoc L w (pFin L a) = pLoc L w (pFin L b)) : a = b := by
  apply Prod.ext
  · exact (infEq L).symm.injective hi
  · apply Subtype.ext
    funext w
    exact hf w

private theorem det_mL (x : UA L 2) (w : Plc L) :
    (mL w x).det = pLoc L w (pFin L ((x : GL (Fin 2) (Ad L)) : Matrix (Fin 2) (Fin 2) (Ad L)).det) := by
  have h : mL w x = ((pLoc L w).comp (pFin L)).mapMatrix ((x : GL (Fin 2) (Ad L)) : Matrix (Fin 2) (Fin 2) (Ad L)) := rfl
  rw [h, ← RingHom.map_det]
  rfl

private theorem det_inf (x : UA L 2) (hx : x ∈ finU (E := L) (n := 2)) :
    pInf L ((x : GL (Fin 2) (Ad L)) : Matrix (Fin 2) (Fin 2) (Ad L)).det = 1 := by
  have h : (pInf L).mapMatrix ((x : GL (Fin 2) (Ad L)) : Matrix (Fin 2) (Fin 2) (Ad L)) = 1 := by
    have h1 : cInf x = 1 := hx
    exact congrArg (fun y : GL (Fin 2) (Cinf L) => (y : Matrix (Fin 2) (Fin 2) (Cinf L))) h1
  rw [RingHom.map_det, h, Matrix.det_one]

private theorem mem_SUA_iff (x : UA L 2) (hx : x ∈ finU (E := L) (n := 2)) :
    x ∈ SUA L ↔ ∀ w : Plc L, (mL w x).det = 1 := by
  have key : x ∈ SUA L ↔ ((x : GL (Fin 2) (Ad L)) : Matrix (Fin 2) (Fin 2) (Ad L)).det = 1 := by
    show GeneralLinearGroup.det (x : GL (Fin 2) (Ad L)) = 1 ↔ _
    rw [Units.ext_iff]
    rfl
  rw [key]
  constructor
  · intro h w
    rw [det_mL, h, map_one, map_one]
  · intro h
    apply ad_ext
    · rw [det_inf x hx, map_one]
    · intro w
      rw [← det_mL, h w, map_one, map_one]

private theorem mem_KD {K O : Type} [Field K] [CommRing O] [Algebra O K] {Δ : K} (g : DX Δ) (hd : (mt g).det = 1)
    (hi : ∀ i j, IsIntegral O (mt g i j)) : g ∈ KD Δ O := by
  let M : Matrix (Fin 2) (Fin 2) (integralClosure O (Lsq K Δ)) := fun i j => ⟨mt g i j, hi i j⟩
  have hM : ((integralClosure O (Lsq K Δ)).val : integralClosure O (Lsq K Δ) →+* Lsq K Δ).mapMatrix M = mt g := by
    ext i j <;> rfl
  have hdet : M.det = 1 := by
    apply Subtype.ext
    have := RingHom.map_det ((integralClosure O (Lsq K Δ)).val : integralClosure O (Lsq K Δ) →+* Lsq K Δ) M
    rw [hM, hd] at this
    exact this
  refine ⟨GeneralLinearGroup.mk'' M (by rw [hdet]; exact isUnit_one), ?_⟩
  ext i j <;> rfl

private theorem SA_det {Δ : Lp L} (g : SA Δ) (v : Pl (Lp L)) : (mt ((g : DA Δ).1 v)).det = 1 := by
  have h := (Subgroup.mem_iInf.1 g.2) v
  have h2 : GeneralLinearGroup.det (((g : DA Δ).1 v : DX (cv v Δ)) : GL (Fin 2) (Lsq (Kv v) (cv v Δ))) = 1 := h
  exact congrArg Units.val h2

private theorem ex_of (R : RingBr L) (g : SA R.Δ) : ∃ b : ↥(finU (E := L) (n := 2) ⊓ SUA L), ∀ w,
    mL w (b : UA L 2) = (mt ((g : DA R.Δ).1 (un w))).map (R.ρ _ w rfl) := by
  have hun : ∀ v, star (mt ((g : DA R.Δ).1 v)) * mt ((g : DA R.Δ).1 v) = 1 := by
    intro v
    rw [((suIff (Kv v) (cv v R.Δ)).1 _).1, SA_det, one_smul]
  have hint : ∀ᶠ v in Filter.cofinite, ∀ i j, IsIntegral (Ov v) (mt ((g : DA R.Δ).1 v) i j) := by
    refine Filter.Eventually.mono (g : DA R.Δ).2 ?_
    intro v hv
    obtain ⟨m, hm⟩ := hv
    intro i j
    have h : mt ((g : DA R.Δ).1 v) i j = (((m : Matrix (Fin 2) (Fin 2) (integralClosure (Ov v) (Lsq (Kv v) (cv v R.Δ)))) i j : integralClosure (Ov v) (Lsq (Kv v) (cv v R.Δ))) : Lsq (Kv v) (cv v R.Δ)) := by
      exact congrArg (fun z : GL (Fin 2) (Lsq (Kv v) (cv v R.Δ)) => (z : Matrix (Fin 2) (Fin 2) (Lsq (Kv v) (cv v R.Δ))) i j) hm.symm
    rw [h]
    exact ((m : Matrix (Fin 2) (Fin 2) (integralClosure (Ov v) (Lsq (Kv v) (cv v R.Δ)))) i j).2
  obtain ⟨b, hb, hloc⟩ := adEx L R 2 (fun v => mt ((g : DA R.Δ).1 v)) hun hint
  refine ⟨⟨b, hb, ?_⟩, hloc⟩
  refine (mem_SUA_iff b hb).2 fun w => ?_
  rw [hloc w]
  have h := RingHom.map_det (R.ρ _ w rfl) (mt ((g : DA R.Δ).1 (un w)))
  rw [SA_det, map_one] at h
  exact h.symm

private theorem sep_of (x y : ↥(finU (E := L) (n := 2) ⊓ SUA L)) (h : ∀ w, mL w (x : UA L 2) = mL w (y : UA L 2)) : x = y := by
  obtain ⟨-, -, -, -, hsep, hfin, -, -⟩ := uaFacts L 2
  exact Subtype.ext (hsep _ _ (fun w => Units.ext (h w))
    fun τ => (((hfin _).1.1 x.2.1) τ).trans (((hfin _).1.1 y.2.1) τ).symm)

end UpperTheory.V.Z.Sym.Dict.Br

theorem UpperTheory.V.Z.Sym.Dict.Br.bSEx :
    ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (R : RingBr L), ∃ b : SA R.Δ ≃* ↥(finU (E := L) (n := 2) ⊓ SUA L), ∀ g w, mL w (b g : UA L 2) = (mt ((g : DA R.Δ).1 (un w))).map (R.ρ _ w rfl) := by
  intro L _ _ _ R
  choose f hf using ex_of R
  have hmul : ∀ g h, f (g * h) = f g * f h := by
    intro g h
    refine sep_of _ _ fun w => ?_
    have h1 : mL w ((f g * f h : ↥(finU (E := L) (n := 2) ⊓ SUA L)) : UA L 2) = mL w (f g : UA L 2) * mL w (f h : UA L 2) := by
      simp only [mL, Subgroup.coe_mul, map_mul, Units.val_mul]
    rw [h1, hf, hf, hf, ← Matrix.map_mul]
    rfl
  have hinj : Function.Injective f := by
    intro g h e
    have hv : ∀ v, mt ((g : DA R.Δ).1 v) = mt ((h : DA R.Δ).1 v) := by
      intro v
      refine Matrix.ext fun i j => sub_eq_zero.1 (R.ρ_inj v _ fun w hw => ?_)
      subst hw
      have h1 := (hf g w).symm.trans ((congrArg (fun b : ↥(finU (E := L) (n := 2) ⊓ SUA L) => mL w (b : UA L 2)) e).trans (hf h w))
      have h2 := congrFun (congrFun h1 i) j
      rw [map_sub, sub_eq_zero]
      exact h2
    exact Subtype.ext (Subtype.ext (funext fun v => Subtype.ext (Units.ext (hv v))))
  have hsurj : Function.Surjective f := by
    rintro ⟨y, hyF, hyS⟩
    obtain ⟨x, hu, hi, hl⟩ := adSurj L R 2 y
    have hdet : ∀ v, (x v).det = 1 := by
      intro v
      refine sub_eq_zero.1 (R.ρ_inj v _ fun w hw => ?_)
      subst hw
      have h1 := RingHom.map_det (R.ρ _ w rfl) (x (un w))
      have h2 : (R.ρ _ w rfl).mapMatrix (x (un w)) = mL w y := (hl w).symm
      rw [map_sub, map_one, h1, h2, (mem_SUA_iff y hyF).1 hyS w, sub_self]
    choose d hd using fun v => (suIff (Kv v) (cv v R.Δ)).2 (x v) (hu v) (hdet v)
    have hmem : ∀ᶠ v in Filter.cofinite, d v ∈ KD (cv v R.Δ) (Ov v) :=
      hi.mono fun v hv => mem_KD (d v) (by rw [hd]; exact hdet v) (by rw [hd]; exact hv)
    let g0 : DA R.Δ := ⟨d, hmem⟩
    have hg0 : g0 ∈ SA R.Δ := by
      refine Subgroup.mem_iInf.2 fun v => ?_
      show GeneralLinearGroup.det ((d v : DX (cv v R.Δ)) : GL (Fin 2) (Lsq (Kv v) (cv v R.Δ))) = 1
      refine Units.ext ?_
      show (mt (d v)).det = 1
      rw [hd]
      exact hdet v
    refine ⟨⟨g0, hg0⟩, sep_of _ _ fun w => ?_⟩
    rw [hf]
    show (mt (d (un w))).map (R.ρ _ w rfl) = mL w y
    rw [hd, hl]
  exact ⟨MulEquiv.ofBijective (MonoidHom.mk' f hmul) ⟨hinj, hsurj⟩, fun g w => hf g w⟩
end

section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil Formalism.BasicNotions Matrix
open UpperTheory.V UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict UpperTheory.V.Z.Sym.Dict.Br UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob
open UpperTheory.V.W (Plc Lp)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem star_int {L : Type} [Field L] [NumberField L] (v : Pl L) (Δ : Kv v) (x : Lsq (Kv v) Δ)
    (h : IsIntegral (Ov v) x) : IsIntegral (Ov v) (star x) := by
  refine IsIntegral.map_of_comp_eq (RingHom.id (Ov v)) (starRingEnd (Lsq (Kv v) Δ)) ?_ h
  refine RingHom.ext fun a => ?_
  apply QuadraticAlgebra.ext <;> simp [Algebra.algebraMap_eq_smul_one, QuadraticAlgebra.re_star, QuadraticAlgebra.im_star, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one, starRingEnd_apply]

section
variable {L : Type} [Field L] [NumberField L] [IsCMField L] (R : RingBr L)

private theorem ext3 (x y : UA L 3) (hx : x ∈ finU (E := L) (n := 3)) (hy : y ∈ finU (E := L) (n := 3)) (h : ∀ w : Plc L, mL w x = mL w y) : x = y := by
  obtain ⟨-, -, -, -, hext, hfin, -⟩ := uaFacts L 3
  refine hext x y (fun w => Units.ext (h w)) fun τ => ?_
  rw [((hfin x).1).1 hx τ, ((hfin y).1).1 hy τ]

private theorem un3 (g : GA R.Δ) (v : Pl (Lp L)) : star (g.1 v : Matrix (Fin 3) (Fin 3) (Lsq (Kv v) (cv v R.Δ))) * (g.1 v : Matrix (Fin 3) (Fin 3) (Lsq (Kv v) (cv v R.Δ))) = 1 :=
  Matrix.UnitaryGroup.star_mul_self (g.1 v)

private theorem co3 (g : GA R.Δ) : ∀ᶠ v in Filter.cofinite, ∀ i j, IsIntegral (Ov v) ((g.1 v : Matrix (Fin 3) (Fin 3) (Lsq (Kv v) (cv v R.Δ))) i j) := by
  have h : ∀ᶠ v in Filter.cofinite, g.1 v ∈ KU (Ov v) (cv v R.Δ) := g.2
  exact h.mono fun v h i j => (h i j).1

private theorem ex3 (g : GA R.Δ) : ∃ f ∈ finU (E := L) (n := 3), ∀ w, mL w f = (g.1 (un w) : Matrix (Fin 3) (Fin 3) _).map (R.ρ _ w rfl) := by
  exact adEx L R 3 (fun v => (g.1 v : Matrix (Fin 3) (Fin 3) (Lsq (Kv v) (cv v R.Δ)))) (un3 R g) (co3 R g)

private noncomputable def f3 (g : GA R.Δ) : UA L 3 := (ex3 R g).choose
private theorem finite_matrix_mem_unitary (g : GA R.Δ) : f3 R g ∈ finU (E := L) (n := 3) := (ex3 R g).choose_spec.1
private theorem finite_part_isomorphism_local (g : GA R.Δ) (w : Plc L) : mL w (f3 R g) = (g.1 (un w) : Matrix (Fin 3) (Fin 3) _).map (R.ρ _ w rfl) := (ex3 R g).choose_spec.2 w

private theorem mL_mul (w : Plc L) (x y : UA L 3) : mL w (x * y) = mL w x * mL w y := by
  simp only [mL, map_mul, Units.val_mul]

private theorem finite_part_isomorphism_mul (g h : GA R.Δ) : f3 R (g * h) = f3 R g * f3 R h := by
  refine ext3 _ _ (finite_matrix_mem_unitary R _) (mul_mem (finite_matrix_mem_unitary R _) (finite_matrix_mem_unitary R _)) fun w => ?_
  rw [mL_mul, finite_part_isomorphism_local, finite_part_isomorphism_local, finite_part_isomorphism_local]
  exact Matrix.map_mul (f := R.ρ _ w rfl)

private theorem finite_part_isomorphism_injective (g h : GA R.Δ) (e : f3 R g = f3 R h) : g = h := by
  refine Subtype.ext (funext fun v => Subtype.ext ?_)
  refine Matrix.ext fun i j => ?_
  rw [← sub_eq_zero]
  refine R.ρ_inj v _ fun w hw => ?_
  subst hw
  have := congrFun (congrFun ((finite_part_isomorphism_local R g w).symm.trans ((congrArg (mL w) e).trans (finite_part_isomorphism_local R h w))) i) j
  simpa [sub_eq_zero] using this

private theorem finite_part_isomorphism_surjective (y : UA L 3) (hy : y ∈ finU (E := L) (n := 3)) : ∃ g, f3 R g = y := by
  obtain ⟨x, hx, hi, hl⟩ := adSurj L R 3 y
  have hu : ∀ v, x v ∈ Matrix.unitaryGroup (Fin 3) (Lsq (Kv v) (cv v R.Δ)) := fun v =>
    Matrix.mem_unitaryGroup_iff'.2 (hx v)
  let g : GA R.Δ := ⟨fun v => ⟨x v, hu v⟩, hi.mono fun v h i j => ⟨h i j, star_int v _ _ (h i j)⟩⟩
  refine ⟨g, ext3 _ _ (finite_matrix_mem_unitary R g) hy fun w => ?_⟩
  rw [finite_part_isomorphism_local, hl]

end

theorem UpperTheory.V.Z.Sym.Dict.Br.bGEx :
    ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (R : RingBr L), ∃ b : GA R.Δ ≃* finU (E := L) (n := 3), ∀ g w, mL w (b g : UA L 3) = (g.1 (un w) : Matrix (Fin 3) (Fin 3) _).map (R.ρ _ w rfl) := by
  intro L _ _ _ R
  let b : GA R.Δ →* finU (E := L) (n := 3) := MonoidHom.mk' (fun g => ⟨f3 R g, finite_matrix_mem_unitary R g⟩) fun g h => Subtype.ext (finite_part_isomorphism_mul R g h)
  have hb : Function.Bijective b := ⟨fun g h e => finite_part_isomorphism_injective R g h (congrArg Subtype.val e), fun y => by
    obtain ⟨g, hg⟩ := finite_part_isomorphism_surjective R y.1 y.2
    exact ⟨g, Subtype.ext hg⟩⟩
  exact ⟨MulEquiv.ofBijective b hb, fun g w => finite_part_isomorphism_local R g w⟩
end

section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil Formalism.BasicNotions Matrix
open UpperTheory.V UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict UpperTheory.V.Z.Sym.Dict.Br UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob
open UpperTheory.V.W (Plc Lp)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Z.Sym.Dict.Br

private theorem cof_val (F : Type) [Field F] [NumberField F] (a : F) (ha : a ≠ 0) :
    ∀ᶠ v : Pl F in Filter.cofinite, v.valuation F a = 1 := by
  have h1 := HeightOneSpectrum.Support.finite (𝓞 F) a
  have h2 := HeightOneSpectrum.Support.finite (𝓞 F) a⁻¹
  have h3 : ((HeightOneSpectrum.Support (𝓞 F) a) ∪ (HeightOneSpectrum.Support (𝓞 F) a⁻¹))ᶜ ∈ Filter.cofinite (α := Pl F) := by
    rw [Filter.mem_cofinite, compl_compl]
    exact h1.union h2
  filter_upwards [h3] with v hv
  simp only [Set.mem_compl_iff, Set.mem_union, not_or, HeightOneSpectrum.Support, Set.mem_setOf_eq, not_lt] at hv
  apply le_antisymm hv.1
  have := hv.2
  rw [map_inv₀] at this
  have h0 : v.valuation F a ≠ 0 := by simpa using ha
  exact (inv_le_one₀ (zero_lt_iff.2 h0)).1 this

private theorem unit_of_val (F : Type) [Field F] [NumberField F] (v : Pl F) (a : F) (h : v.valuation F a = 1) :
    ∃ u : (Ov v)ˣ, algebraMap (Ov v) (Kv v) u = cv v a := by
  have h1 : Valued.v (cv v a) = 1 := by
    rw [← h]
    exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v a
  have h0 : cv v a ≠ 0 := by
    intro h0
    rw [h0] at h1
    simp at h1
  have h2 : Valued.v (cv v a)⁻¹ = 1 := by rw [map_inv₀, h1, inv_one]
  refine ⟨⟨⟨cv v a, h1.le⟩, ⟨(cv v a)⁻¹, h2.le⟩, ?_, ?_⟩, rfl⟩
  · exact Subtype.ext (mul_inv_cancel₀ h0)
  · exact Subtype.ext (inv_mul_cancel₀ h0)

private theorem conj_cmp {A A' : Type} [CommRing A] [CommRing A'] (ρ : A →+* A') (c : A)
    (Y G : GL (Fin 2) A) (P Q R : GL (Fin 2) A')
    (hP : (P : Matrix (Fin 2) (Fin 2) A') = (((Y⁻¹ * G * Y : GL (Fin 2) A)) : Matrix (Fin 2) (Fin 2) A).map ρ)
    (hQ : (Q : Matrix (Fin 2) (Fin 2) A') = (G : Matrix (Fin 2) (Fin 2) A).map ρ)
    (hR : (R : Matrix (Fin 2) (Fin 2) A') = (c • (Y : Matrix (Fin 2) (Fin 2) A)).map ρ) :
    P = R⁻¹ * Q * R := by
  have key : R * P = Q * R := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, hP, hQ, hR, ← Matrix.map_mul, ← Matrix.map_mul]
    congr 1
    have : (Y : Matrix (Fin 2) (Fin 2) A) * ((Y⁻¹ * G * Y : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) = (G : Matrix (Fin 2) (Fin 2) A) * (Y : Matrix (Fin 2) (Fin 2) A) := by
      rw [← Units.val_mul, ← Units.val_mul]
      congr 1
      group
    rw [Matrix.smul_mul, this, Matrix.mul_smul]
  rw [mul_assoc, eq_inv_mul_iff_mul_eq, key]

end UpperTheory.V.Z.Sym.Dict.Br

theorem UpperTheory.V.Z.Sym.Dict.Br.okConj :
    ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (B : Bridge L), ∀ x ∈ finU (E := L) (n := 2), ∃ y : DA B.Δ, (∀ v, (∀ w, un w = v → cLoc w x = 1) → y.1 v = 1) ∧ ∀ g : SA B.Δ, ∃ g' : SA B.Δ, (g' : DA B.Δ) = y⁻¹ * g * y ∧ (B.bS g' : UA L 2) = x⁻¹ * B.bS g * x := by
  intro L _ _ _ B x hx
  obtain ⟨X, hXu, hXi, hXw⟩ := adSurj L B.toRingBr 2 x
  have hΔ : B.Δ ≠ 0 := by
    intro h0
    have hω : (QuadraticAlgebra.omega : Lsq (Lp L) B.Δ) * QuadraticAlgebra.omega = 0 := by
      ext <;> simp [h0]
    have h1 : B.e QuadraticAlgebra.omega * B.e QuadraticAlgebra.omega = 0 := by
      rw [← map_mul, hω, map_zero]
    have h2 : B.e QuadraticAlgebra.omega = 0 := mul_self_eq_zero.1 h1
    have h3 : (QuadraticAlgebra.omega : Lsq (Lp L) B.Δ) = 0 := (map_eq_zero_iff _ B.e.injective).1 h2
    simpa using congrArg QuadraticAlgebra.im h3
  have h2F : (2 : Lp L) ≠ 0 := two_ne_zero
  have h2 : ∀ v : Pl (Lp L), (2 : Kv v) ≠ 0 := by
    intro v h0
    apply h2F
    apply (cv v).injective
    rw [map_ofNat, map_zero, h0]
  have hΔv : ∀ v : Pl (Lp L), cv v B.Δ ≠ 0 := fun v h0 => hΔ ((map_eq_zero _).1 h0)
  choose Y c hYc hY1 hYK using fun v : Pl (Lp L) => h90 (Ov v) (Kv v) (cv v B.Δ) (h2 v) (hΔv v) (X v) (hXu v)
  have hYA : Y ∈ RP (fun v : Pl (Lp L) => DX (cv v B.Δ)) fun v => KD (cv v B.Δ) (Ov v) := by
    show ∀ᶠ v in Filter.cofinite, Y v ∈ KD (cv v B.Δ) (Ov v)
    filter_upwards [hXi, cof_val (Lp L) B.Δ hΔ, cof_val (Lp L) 2 h2F] with v hi hv h2v
    obtain ⟨h1, -, -, h4⟩ := locBase (Lp L) v
    haveI := h1
    have h2n : (2 : 𝓞 (Lp L)) ∉ v.asIdeal := by
      intro hm
      have := (HeightOneSpectrum.valuation_lt_one_iff_mem (K := Lp L) v (2 : 𝓞 (Lp L))).2 hm
      simp only [map_ofNat] at this
      exact this.ne h2v
    exact hYK v (h4 h2n) (unit_of_val (Lp L) v B.Δ hv) hi
  refine ⟨⟨Y, hYA⟩, ?_, ?_⟩
  · intro v hv
    apply hY1 v
    refine Matrix.ext fun i j => ?_
    rw [← sub_eq_zero]
    apply B.ρ_inj v
    intro w h
    subst h
    have := hXw w
    have h3 : mL w x = 1 := by
      simp only [mL, hv w rfl]
      rfl
    rw [map_sub, sub_eq_zero]
    have h4 := congrFun (congrFun (this.symm.trans h3) i) j
    rw [Matrix.map_apply] at h4
    rw [h4]
    by_cases hij : i = j
    · subst hij; simp
    · simp [hij]
  · intro g
    have hmem : ((⟨Y, hYA⟩ : DA B.Δ)⁻¹ * (g : DA B.Δ) * ⟨Y, hYA⟩) ∈ SA B.Δ := by
      have hg := g.2
      simp only [SA, Subgroup.mem_iInf] at hg ⊢
      intro v
      have := hg v
      simp only [Subgroup.mem_comap, SU, MonoidHom.mem_ker, MonoidHom.comp_apply] at this ⊢
      simp only [map_mul, map_inv, this, mul_one, inv_mul_cancel]
    refine ⟨⟨_, hmem⟩, rfl, ?_⟩
    have hF := (uaFacts L 2)
    have hext := hF.2.2.2.2.1
    have hfin := hF.2.2.2.2.2.1
    apply hext
    · intro w
      rw [map_mul, map_mul, map_inv]
      apply conj_cmp (B.ρ _ w rfl) (c (un w) : Lsq (Kv (un w)) (cv (un w) B.Δ)) ((Y (un w) : DX _) : GL (Fin 2) _) (((g : DA B.Δ).1 (un w) : DX _) : GL (Fin 2) _)
      · exact B.bS_loc _ w
      · exact B.bS_loc _ w
      · rw [← hYc]
        exact hXw w
    · intro τ
      have a1 := ((hfin _).1.1 (B.bS ⟨_, hmem⟩).2.1) τ
      have a2 := ((hfin _).1.1 (B.bS g).2.1) τ
      have a3 := ((hfin _).1.1 hx) τ
      rw [a1, map_mul, map_mul, map_inv, a2, a3]
      simp
end
