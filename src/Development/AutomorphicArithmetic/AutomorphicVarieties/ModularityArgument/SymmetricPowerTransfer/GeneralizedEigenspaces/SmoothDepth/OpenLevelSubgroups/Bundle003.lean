module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.SmoothDepth.ContCoef
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceUnitaryLocalPointsEquivGL
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1742
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle092
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle307
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL Formalism.BasicNotions
open UpperTheory.V.W (Plc Lp)
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.V.Z.Sym.Al

private theorem exists_finPart {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} :
    ∃ p : UA L n → finU (E := L) (n := n), Continuous p ∧ p 1 = 1 ∧ ∀ x, (p x : UA L n)⁻¹ * x ∈ infU L n := by
  have hfin : Continuous (finGL L n) :=
    Continuous.units_map _ (continuous_const.add (continuous_id.matrix_map
      (continuous_const.prodMk continuous_id : Continuous fun x : Af L => ((0, x) : InfiniteAdeleRing L × Af L))))
  refine ⟨fun x => ⟨⟨finGL L n (Matrix.GeneralLinearGroup.map (pFin L) x.1),
    GlobalTheory.SplitPts.finGL_mem_UA _ fun u => GlobalTheory.SplitPts.comp_eq x u⟩, MonoidHom.mem_ker.2 (pInf_finGL _)⟩,
    Continuous.subtype_mk (Continuous.subtype_mk
      (hfin.comp (GlobalTheory.DefU.continuous_map_pFin.comp continuous_subtype_val)) _) _, ?_, fun x => ?_⟩
  · refine Subtype.ext (Subtype.ext ?_)
    change finGL L n (Matrix.GeneralLinearGroup.map (pFin L) 1) = 1
    rw [map_one, map_one]
  · change Matrix.GeneralLinearGroup.map (pFin L)
      ((finGL L n (Matrix.GeneralLinearGroup.map (pFin L) x.1))⁻¹ * x.1) = 1
    rw [map_mul, map_inv, pFin_finGL, inv_mul_cancel]

private theorem continuous_infC {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} :
    Continuous (infC L n) := by
  have hτ : ∀ τ : L →+* ℂ, Continuous (cEmb (E := L) (n := n) τ) := fun τ => by
    have h1 : Continuous (coord (E := L) τ) := by
      unfold coord
      split_ifs
      · exact continuous_apply _
      · exact Complex.continuous_conj.comp (continuous_apply _)
    have h2 : Continuous (pInf L) := continuous_pi fun w =>
      (InfinitePlace.Completion.isometryEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)).continuous.comp
        ((continuous_apply w).comp continuous_fst)
    exact (Continuous.units_map _ (continuous_id.matrix_map h1)).comp
      ((Continuous.units_map _ (continuous_id.matrix_map h2)).comp continuous_subtype_val)
  exact continuous_pi fun v => hτ v.embedding

private theorem infC_of_fin {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {k : UA L n}
    (hk : k ∈ finU (E := L) (n := n)) : infC L n k = 1 :=
  funext fun v => by
    change Matrix.GeneralLinearGroup.map (coord v.embedding) (cInf k) = 1
    rw [MonoidHom.mem_ker.1 hk, map_one]

theorem UpperTheory.V.Z.Sym.Al.coefAut :
    ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (R : Representation ℂ (InfinitePlace L → GL (Fin n) ℂ) V), ContCoef R → ∀ U, IsLevel U → ∀ φ : UA L n → V, IsAF R U φ →
        ∀ f : V →ₗ[ℂ] ℂ, IsAutFormU (f ∘ φ) := by
  intro L _ _ _ n V _ _ _ R hR U hU φ hφ f
  obtain ⟨p, hp, hp1, hp2⟩ := exists_finPart (L := L) (n := n)
  have hU1 : {x : finU (E := L) (n := n) | (x : UA L n) ∈ U} ∈ nhds (1 : finU (E := L) (n := n)) := hU.2.mem_nhds U.one_mem

  have hsm : ∀ᶠ z in nhds (1 : UA L n), ∀ g, φ (g * z) = R (infC L n z⁻¹) (φ g) := by
    have hUp : {x : finU (E := L) (n := n) | (x : UA L n) ∈ U} ∈ nhds (p 1) := by rwa [hp1]
    filter_upwards [(hp.tendsto 1).eventually hUp] with z hz g
    have h1 := hφ.inf _ (hp2 z) (g * (p z : UA L n))
    rw [hφ.level _ hz g, mul_assoc, mul_inv_cancel_left] at h1
    have e : infC L n ((p z : UA L n)⁻¹ * z)⁻¹ = infC L n z⁻¹ := by
      rw [mul_inv_rev, inv_inv, map_mul, infC_of_fin (p z).2, mul_one]
    rw [h1, e]
  refine ⟨?_, fun γ hγ g => congrArg f (hφ.left γ hγ g), ?_, ?_⟩
  · refine continuous_iff_continuousAt.2 fun g0 => ?_
    have hc : Continuous fun g : UA L n => f (R (infC L n (g⁻¹ * g0)) (φ g0)) :=
      (hR (φ g0) f).comp (continuous_infC.comp (continuous_inv.mul continuous_const))
    refine hc.continuousAt.congr ?_
    have ht : Filter.Tendsto (fun g : UA L n => g0⁻¹ * g) (nhds g0) (nhds 1) := by
      have : Continuous fun g : UA L n => g0⁻¹ * g := continuous_const.mul continuous_id
      simpa only [inv_mul_cancel] using this.tendsto g0
    filter_upwards [ht.eventually hsm] with g hg
    have e := hg g0
    rw [mul_inv_cancel_left, mul_inv_rev, inv_inv] at e
    rw [Function.comp_apply, e]
  · refine isOpen_stab_of_mem_nhds ((RU L n).comp (finU (E := L) (n := n)).subtype) _ ?_
    filter_upwards [hU1] with k hk
    funext g
    exact congrArg f (hφ.level _ hk g)
  · let C : Module.Dual ℂ V →ₗ[ℂ] (UA L n → ℂ) :=
      { toFun := fun μ g => μ (φ g)
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    refine Submodule.finiteDimensional_of_le (S₂ := LinearMap.range C) (Submodule.span_le.2 ?_)
    rintro _ ⟨k, rfl⟩
    refine ⟨f ∘ₗ R (infC L n (k : UA L n)⁻¹), ?_⟩
    funext g
    change f (R (infC L n (k : UA L n)⁻¹) (φ g)) = f (φ (g * k))
    rw [hφ.inf _ k.2 g]
end

section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL Formalism.BasicNotions
open UpperTheory.V.W (Plc Lp)
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.V.Z.Sym.Al

noncomputable section

namespace UpperTheory.V.Z.Sym.Al.FactorizationTer

open GlobalTheory.SplitPts GlobalTheory.BCT.GlobLev

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

private theorem ua_ext {g h : UA E n} (h1 : cInf g = cInf h) (h2 : ∀ u, cLoc u g = cLoc u h) : g = h := by
  refine Subtype.ext (ga_ext h1 ?_)
  refine Units.ext (matAf_ext fun u => ?_)
  exact congrArg Units.val (h2 u)


open Classical in
private def idem (P : HeightOneSpectrum (𝓞 E) → Prop) : Af E :=
  ⟨fun u => if P u then 1 else 0, Filter.Eventually.of_forall fun u => by
    dsimp only
    split_ifs
    · exact one_mem _
    · exact zero_mem _⟩

open Classical in
private theorem pLoc_idem (P : HeightOneSpectrum (𝓞 E) → Prop) (u : HeightOneSpectrum (𝓞 E)) :
    pLoc E u (idem P) = if P u then 1 else 0 := rfl

private def cutM (P : HeightOneSpectrum (𝓞 E) → Prop) (A : Matrix (Fin n) (Fin n) (Af E)) :
    Matrix (Fin n) (Fin n) (Af E) := idem P • A + (1 - idem P) • 1

private theorem map_cutM_pos {P : HeightOneSpectrum (𝓞 E) → Prop} (A : Matrix (Fin n) (Fin n) (Af E))
    {u : HeightOneSpectrum (𝓞 E)} (h : P u) :
    RingHom.mapMatrix (pLoc E u) (cutM P A) = RingHom.mapMatrix (pLoc E u) A := by
  ext i j
  simp [cutM, Matrix.add_apply, Matrix.smul_apply, pLoc_idem, h]

private theorem map_cutM_neg {P : HeightOneSpectrum (𝓞 E) → Prop} (A : Matrix (Fin n) (Fin n) (Af E))
    {u : HeightOneSpectrum (𝓞 E)} (h : ¬ P u) :
    RingHom.mapMatrix (pLoc E u) (cutM P A) = 1 := by
  have h0 : pLoc E u (idem P) = 0 := by rw [pLoc_idem, if_neg h]
  refine Matrix.ext fun i j => ?_
  change pLoc E u (idem P * A i j + (1 - idem P) * (1 : Matrix (Fin n) (Fin n) (Af E)) i j) =
    (1 : Matrix (Fin n) (Fin n) (u.adicCompletion E)) i j
  rw [map_add (f := _), map_mul, map_mul, map_sub, map_one, h0, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

private theorem cutM_mul (P : HeightOneSpectrum (𝓞 E) → Prop) {A B : Matrix (Fin n) (Fin n) (Af E)}
    (h : A * B = 1) : cutM P A * cutM P B = 1 := by
  refine matAf_ext fun u => ?_
  rw [map_mul, map_one]
  by_cases hu : P u
  · rw [map_cutM_pos _ hu, map_cutM_pos _ hu, ← map_mul, h, map_one]
  · rw [map_cutM_neg _ hu, map_cutM_neg _ hu, one_mul]

private def cut (P : HeightOneSpectrum (𝓞 E) → Prop) (k : GL (Fin n) (Af E)) : GL (Fin n) (Af E) where
  val := cutM P k.val
  inv := cutM P (k⁻¹).val
  val_inv := cutM_mul P (by simp)
  inv_val := cutM_mul P (by simp)

private theorem under_conj (u : HeightOneSpectrum (𝓞 E)) :
    (conjSrc (conjE E) u).under (𝓞 (maximalRealSubfield E)) = u.under (𝓞 (maximalRealSubfield E)) :=
  (GlobalTheory.Mem.Chr.under_eq_iff_conjPl (IsCMField.complexConj E)
    (Algebra.IsQuadraticExtension.finrank_eq_two _ _) (IsCMField.complexConj_ne_one E) u _).2
      (Or.inr (conjPl_self_conjSrc u))

private theorem exists_part (w : HeightOneSpectrum (𝓞 E)) (g : UA E n) :
    ∃ x : UA E n, cInf x = 1 ∧
      (∀ u, u.under (𝓞 (maximalRealSubfield E)) = w.under (𝓞 (maximalRealSubfield E)) → cLoc u x = cLoc u g) ∧
      ∀ u, u.under (𝓞 (maximalRealSubfield E)) ≠ w.under (𝓞 (maximalRealSubfield E)) → cLoc u x = 1 := by
  set P : HeightOneSpectrum (𝓞 E) → Prop := fun u =>
    u.under (𝓞 (maximalRealSubfield E)) = w.under (𝓞 (maximalRealSubfield E)) with hP
  set k : GL (Fin n) (Af E) := cut P (Matrix.GeneralLinearGroup.map (pFin E) g.1) with hk
  have hpos : ∀ u, P u → Matrix.GeneralLinearGroup.map (pLoc E u) k = cLoc u g := fun u hu =>
    Units.ext (map_cutM_pos _ hu)
  have hneg : ∀ u, ¬ P u → Matrix.GeneralLinearGroup.map (pLoc E u) k = 1 := fun u hu =>
    Units.ext (map_cutM_neg _ hu)
  have hmem : finGL E n k ∈ UA E n := by
    refine finGL_mem_UA k fun u => ?_
    by_cases hu : P u
    · have hc : P (conjSrc (conjE E) u) := (under_conj u).trans hu
      rw [hpos u hu, hpos _ hc]
      exact comp_eq g u
    · have hc : ¬ P (conjSrc (conjE E) u) := fun h => hu ((under_conj u).symm.trans h)
      rw [hneg u hu, hneg _ hc]
      simp
  have hloc : ∀ u, cLoc u (⟨_, hmem⟩ : UA E n) = Matrix.GeneralLinearGroup.map (pLoc E u) k := fun u => by
    change Matrix.GeneralLinearGroup.map ((pLoc E u).comp (pFin E)) (finGL E n k) = _
    exact Units.ext (congrArg (fun M : GL (Fin n) (Af E) => RingHom.mapMatrix (pLoc E u) M.val) (pFin_finGL k))
  exact ⟨⟨_, hmem⟩, pInf_finGL k, fun u hu => (hloc u).trans (hpos u hu),
    fun u hu => (hloc u).trans (hneg u hu)⟩

end UpperTheory.V.Z.Sym.Al.FactorizationTer

end

theorem UpperTheory.V.Z.Sym.Al.factor :
    ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (w : Plc L),
        (∀ x ∈ locU n w, ∀ y ∈ away n w, x * y = y * x) ∧
        (∀ g : UA L n, ∃ x ∈ locU n w, ∃ y ∈ away n w, g = x * y) ∧
        (∀ w' : Plc L, w'.under (𝓞 (Lp L)) ≠ w.under (𝓞 (Lp L)) → locU n w' ≤ away n w) ∧ infU L n ≤ away n w ∧
        (∀ x ∈ locU n w, x ∈ Kall (L := L) n ↔ cLoc w x ∈ GlobalTheory.LFun.KGL w (n := n)) ∧
        ∀ x ∈ locU n w, ∀ y ∈ away n w, (x * y ∈ Kall (L := L) n ↔ x ∈ Kall (L := L) n ∧ y ∈ Kall (L := L) n) := by
  intro L _ _ _ n w
  have hfin : ∀ {x : UA L n}, x ∈ locU n w → cInf x = 1 := fun hx => (Subgroup.mem_inf.1 hx).1
  have hout : ∀ {x : UA L n}, x ∈ locU n w → ∀ u : Plc L, u.under (𝓞 (Lp L)) ≠ w.under (𝓞 (Lp L)) →
      cLoc u x = 1 := fun hx u hu =>
    MonoidHom.mem_ker.1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 (Subgroup.mem_inf.1 hx).2 u) hu)
  have hin : ∀ {y : UA L n}, y ∈ away n w → ∀ u : Plc L, u.under (𝓞 (Lp L)) = w.under (𝓞 (Lp L)) →
      cLoc u y = 1 := fun hy u hu =>
    MonoidHom.mem_ker.1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hy u) hu)
  have haway : ∀ {y : UA L n}, (∀ u : Plc L, u.under (𝓞 (Lp L)) = w.under (𝓞 (Lp L)) → cLoc u y = 1) →
      y ∈ away n w := fun h =>
    Subgroup.mem_iInf.2 fun u => Subgroup.mem_iInf.2 fun hu => MonoidHom.mem_ker.2 (h u hu)
  have hK : ∀ {x : UA L n}, x ∈ Kall (L := L) n → ∀ u : Plc L, cLoc u x ∈ GlobalTheory.LFun.KGL u (n := n) := fun hx u =>
    Subgroup.mem_comap.1 (Subgroup.mem_iInf.1 (Subgroup.mem_inf.1 hx).2 u)
  have hKmk : ∀ {x : UA L n}, x ∈ finU (E := L) (n := n) → (∀ u : Plc L, cLoc u x ∈ GlobalTheory.LFun.KGL u (n := n)) → x ∈ Kall (L := L) n :=
    fun h1 h2 => Subgroup.mem_inf.2 ⟨h1, Subgroup.mem_iInf.2 fun u => Subgroup.mem_comap.2 (h2 u)⟩
  have hKf : ∀ {x : UA L n}, x ∈ Kall (L := L) n → x ∈ finU (E := L) (n := n) := fun hx => (Subgroup.mem_inf.1 hx).1
  refine ⟨fun x hx y hy => ?_, fun g => ?_, fun w' hw' x hx => ?_, fun x hx => ?_, fun x hx => ⟨fun h => hK h w, fun h => ?_⟩,
    fun x hx y hy => ⟨fun h => ?_, fun h => mul_mem h.1 h.2⟩⟩
  · refine FactorizationTer.ua_ext ?_ fun u => ?_
    · rw [map_mul, map_mul, hfin hx, one_mul, mul_one]
    · rw [map_mul, map_mul]
      by_cases hu : u.under (𝓞 (Lp L)) = w.under (𝓞 (Lp L))
      · rw [hin hy u hu, one_mul, mul_one]
      · rw [hout hx u hu, one_mul, mul_one]
  · obtain ⟨x, h1, h2, h3⟩ := FactorizationTer.exists_part w g
    refine ⟨x, Subgroup.mem_inf.2 ⟨h1, Subgroup.mem_iInf.2 fun u => Subgroup.mem_iInf.2 fun hu =>
      MonoidHom.mem_ker.2 (h3 u hu)⟩, x⁻¹ * g, haway fun u hu => ?_, by group⟩
    rw [map_mul, map_inv, h2 u hu, inv_mul_cancel]
  · refine haway fun u hu => ?_
    exact MonoidHom.mem_ker.1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 (Subgroup.mem_inf.1 hx).2 u)
      (by rw [hu]; exact hw'.symm))
  · refine haway fun u _ => ?_
    have h : Matrix.GeneralLinearGroup.map (pFin L) x.1 = 1 := hx
    have h' := congrArg (Matrix.GeneralLinearGroup.map (pLoc L u)) h
    rw [map_one] at h'
    exact h'
  · refine hKmk (Subgroup.mem_inf.1 hx).1 fun u => ?_
    by_cases hu : u.under (𝓞 (Lp L)) = w.under (𝓞 (Lp L))
    · rcases GlobalTheory.BCT.GlobLev.eq_or_eq_conjSrc hu with e | e
      · subst e
        exact h
      · subst e
        exact GlobalTheory.BCT.GlobLev.integral_conjSrc x w h
    · rw [hout hx u hu]
      exact one_mem _
  · have hf : cInf (x * y) = 1 := hKf h
    rw [map_mul, hfin hx, one_mul] at hf
    refine ⟨hKmk (Subgroup.mem_inf.1 hx).1 fun u => ?_, hKmk hf fun u => ?_⟩
    · by_cases hu : u.under (𝓞 (Lp L)) = w.under (𝓞 (Lp L))
      · have := hK h u
        rwa [map_mul, hin hy u hu, mul_one] at this
      · rw [hout hx u hu]
        exact one_mem _
    · by_cases hu : u.under (𝓞 (Lp L)) = w.under (𝓞 (Lp L))
      · rw [hin hy u hu]
        exact one_mem _
      · have := hK h u
        rwa [map_mul, hout hx u hu, one_mul] at this
end

section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL Formalism.BasicNotions
open UpperTheory.V.W (Plc Lp)
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.V.Z.Sym.Al

theorem UpperTheory.V.Z.Sym.Al.afFin :
    ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (R : Representation ℂ (InfinitePlace L → GL (Fin n) ℂ) V) (U : Subgroup (UA L n)), IsLevel U → FiniteDimensional ℂ (AF R U) := by
  intro L _ _ _ n V _ _ _ R U hU
  obtain ⟨S, hS⟩ := GlobalTheory.T.definiteUnitary_classSet_finite L n (U.subgroupOf (finU (E := L) (n := n))) hU.2
  let T : AF R U →ₗ[ℂ] (S → V) :=
    { toFun := fun φ s => φ.1 s.1
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  refine FiniteDimensional.of_injective T ((injective_iff_map_eq_zero T).2 fun φ h0 => ?_)
  refine Subtype.ext (funext fun g => ?_)
  obtain ⟨γ, hγ, s, hs, x, hx, k, hk, rfl⟩ := hS g
  have hφ : IsAF R U φ.1 := φ.2
  have hz : φ.1 s = 0 := congrFun h0 ⟨s, hs⟩
  rw [hφ.level _ (Subgroup.mem_subgroupOf.1 hk), hφ.inf x hx, hφ.left γ hγ, hz, map_zero]
  rfl
end
