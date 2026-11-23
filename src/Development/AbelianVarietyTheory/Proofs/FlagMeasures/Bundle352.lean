module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalIsometryExtendsLocalIsometry
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitriangularChangeRationalFlagIffRationalUnipot
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle017
import Formalism.HermitianLattices.HermitianLatticesProofs.AutFinite
import Mathlib.Algebra.AffineMonoid.Basic
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle329
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle342
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc Formalism.L2.SG.TermDef GlobalTheory.LocOver
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.rational_isometry_extends_local_isometry : ∀ (D : D7) (Z : LocDat D), ∀ (p : PlF D), ∀ γ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT, ∃ g, Ext p γ g ∧ LocNG.IsUnitary (locH Z p) g ∧ (∀ g', Ext p γ g' → g' = g) ∧ (∀ Λ : Submodule (𝓞 D.host.E) (VS D).V, LocNG.img (M := Z.M p) g (lattice₂ D Z.M p Λ) = lattice₂ D Z.M p (Formalism.HermitianLatticesTheory.gmap γ Λ)) ∧ ∀ {T : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T), γ ∈ Formalism.L2.SG.NGData.NRat F → g ∈ NU (locH Z p) (scaled Z p (frame F)) := by
  first | exact @GlobalTheory.LocExt.ext_isometry | exact GlobalTheory.LocExt.ext_isometry | (intros; apply GlobalTheory.LocExt.ext_isometry <;> assumption)
end

section

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc Formalism.L2.SG.TermDef GlobalTheory.LocOver
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.unitriangularChange_rationalFlag_iff_rationalUnipotent : ∀ (D : D7) {T : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T), T ≠ 0 → (∀ A : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E, Uni A → ∃ F₁ : LFlag (D.sp.Y 0) D.R.rS T, Chg (frame F) A (frame F₁)) ∧ (∀ F₁ : LFlag (D.sp.Y 0) D.R.rS T, Tri D.host.E (frame F) (frame F₁) ↔ ∃ n ∈ Formalism.L2.SG.NGData.NRat F, ∀ a, frame F₁ a = n (frame F a)) := by
  first | exact @GlobalTheory.FlagChange.flag_change | exact GlobalTheory.FlagChange.flag_change | (intros; apply GlobalTheory.FlagChange.flag_change <;> assumption)
end

section

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.StabFin

section Core

variable {E V : Type} [Field E] [NumberField E] [StarRing E] [AddCommGroup V] [Module E V]
  [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V] [FiniteDimensional E V]

theorem finite_of_fix (hT : V →ₗ⋆[E] V →ₗ[E] E) (U : Submodule E V)
    (hpos : ∀ x ∈ (⨅ u ∈ U, LinearMap.ker (hT u)), x ≠ 0 → 0 < Algebra.trace ℚ E (hT x x))
    (Λ₀ : Submodule (𝓞 E) V) (hΛ : Submodule.IsFullLattice E Λ₀) :
    {h : V ≃ₗ[E] V | h ∈ Formalism.HermitianLatticesTheory.isom hT ∧ (∀ u ∈ U, h u = u) ∧ Formalism.HermitianLatticesTheory.gmap h Λ₀ = Λ₀}.Finite := by
  set W : Submodule E V := ⨅ u ∈ U, LinearMap.ker (hT u) with hWdef
  have memW : ∀ y, y ∈ W ↔ ∀ x ∈ U, hT x y = 0 := fun y => by
    simp [hWdef, Submodule.mem_iInf]
  have hdisj : U ⊓ W = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxU, hxW⟩
    by_contra hx0
    have := hpos x hxW hx0
    rw [(memW x).1 hxW x hxU] at this
    simp at this
  have hsup : U ⊔ W = ⊤ := by
    let b := Module.finBasis E U
    let φ : V →ₗ[E] (Fin (Module.finrank E U) → E) := LinearMap.pi fun i => hT (b i : V)
    have hker : LinearMap.ker φ ≤ W := by
      intro y hy
      rw [memW]
      intro x hx
      have hy' : ∀ i, hT (b i : V) y = 0 := fun i => congrFun (LinearMap.mem_ker.1 hy) i
      have hx' : x = ∑ i, (b.repr ⟨x, hx⟩ i) • (b i : V) := by
        have := congrArg Subtype.val (b.sum_repr ⟨x, hx⟩)
        rw [Submodule.coe_sum] at this
        simp only [Submodule.coe_smul] at this
        exact this.symm

      rw [hx', map_sum, LinearMap.sum_apply]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, hy' i, smul_zero]
    have h1 := LinearMap.finrank_range_add_finrank_ker φ
    have h2 : Module.finrank E (LinearMap.range φ) ≤ Module.finrank E U := by
      refine (Submodule.finrank_le _).trans ?_
      simp
    have h3 := Submodule.finrank_mono hker
    have h4 := Submodule.finrank_sup_add_finrank_inf_eq U W
    rw [hdisj, finrank_bot] at h4
    apply Submodule.eq_top_of_finrank_eq
    have h5 := Submodule.finrank_le (U ⊔ W)
    omega
  have hmul : ∀ v : V, ∃ d : 𝓞 E, d ≠ 0 ∧ d • v ∈ Λ₀ := fun v => by
    have hv : v ∈ Submodule.span E (Λ₀ : Set V) := by rw [Submodule.IsFullLattice.span_eq_top (self := hΛ)]; trivial
    obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span (nonZeroDivisors (𝓞 E)) E _ v hv
    rw [Submodule.span_eq] at ht
    exact ⟨t, nonZeroDivisors.ne_zero t.2, ht⟩
  let L : Submodule (𝓞 E) W := Λ₀.comap (W.subtype.restrictScalars (𝓞 E))
  have hfg : L.FG := by
    apply Submodule.fg_of_fg_map_injective (W.subtype.restrictScalars (𝓞 E)) Subtype.val_injective
    exact hΛ.fg.of_le (Submodule.map_comap_le _ _)
  haveI : Submodule.IsLattice E L := Submodule.IsLattice.of_fg E hfg
  let hW := hT.domRestrict₁₂ W W
  have hposW : ∀ w : W, w ≠ 0 → 0 < Algebra.trace ℚ E (hW w w) := fun w hw =>
    hpos w w.2 fun h0 => hw (Subtype.ext h0)
  obtain ⟨N, hN⟩ := hfg
  have hNL : ∀ n ∈ N, ((n : W) : V) ∈ Λ₀ := fun n hn => by
    have : n ∈ L := hN ▸ Submodule.subset_span hn
    exact this
  have hpres : ∀ h : V ≃ₗ[E] V, h ∈ Formalism.HermitianLatticesTheory.isom hT → (∀ u ∈ U, h u = u) → ∀ w ∈ W, h w ∈ W := by
    intro h hiso hfix w hw
    rw [memW] at hw ⊢
    intro x hx
    rw [← hfix x hx, hiso x w]
    exact hw x hx
  refine Set.Finite.of_finite_image (f := fun (h : V ≃ₗ[E] V) (n : N) => h ((n : W) : V)) ?_ ?_
  · refine (Set.Finite.pi (t := fun n : N => Subtype.val '' {v : W | v ∈ L ∧
        Algebra.trace ℚ E (hW v v) ≤ Algebra.trace ℚ E (hW (n : W) (n : W))})
      fun n => (Formalism.HermitianLatticesTheory.autFinite_short hW hposW L _).image _).subset ?_
    rintro _ ⟨h, ⟨hiso, hfix, hlat⟩, rfl⟩ n _
    refine ⟨⟨h ((n : W) : V), hpres h hiso hfix _ (n : W).2⟩, ⟨?_, ?_⟩, rfl⟩
    · have hm : ((h : V →ₗ[E] V).restrictScalars (𝓞 E)) ((n : W) : V) ∈ Formalism.HermitianLatticesTheory.gmap h Λ₀ :=
        Submodule.mem_map_of_mem (hNL n n.2)
      rw [hlat] at hm
      exact hm
    · show Algebra.trace ℚ E (hT (h ((n : W) : V)) (h ((n : W) : V))) ≤
        Algebra.trace ℚ E (hT ((n : W) : V) ((n : W) : V))
      rw [hiso]
  · rintro h₁ ⟨-, hf1, -⟩ h₂ ⟨-, hf2, -⟩ heq
    let K : Submodule E V := LinearMap.ker ((h₁ : V →ₗ[E] V) - (h₂ : V →ₗ[E] V))
    have memK : ∀ x, x ∈ K ↔ h₁ x = h₂ x := fun x => by
      simp [K, LinearMap.mem_ker, sub_eq_zero]
    have hLK : L ≤ (K.restrictScalars (𝓞 E)).comap (W.subtype.restrictScalars (𝓞 E)) := by
      rw [← hN]
      refine Submodule.span_le.2 fun n hn => ?_
      show ((n : W) : V) ∈ K
      rw [memK]
      exact congrFun heq ⟨n, hn⟩
    have hWK : W ≤ K := by
      intro w hw
      obtain ⟨d, hd0, hd⟩ := hmul w
      have h1 : (⟨d • w, W.smul_of_tower_mem d hw⟩ : W) ∈ L := hd
      have h2 : d • w ∈ K := hLK h1
      rw [← algebraMap_smul E d w] at h2
      exact (Submodule.smul_mem_iff K
        ((map_ne_zero_iff _ (IsFractionRing.injective (𝓞 E) E)).mpr hd0)).1 h2
    have hUK : U ≤ K := fun u hu => by rw [memK, hf1 u hu, hf2 u hu]
    have htop : ⊤ ≤ K := hsup ▸ sup_le hUK hWK
    exact LinearEquiv.ext fun x => (memK x).1 (htop trivial)

end Core

theorem stab_finite : ∀ (D : D7) {T T' : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T) (F' : LFlag (D.sp.Y 0) D.R.rS T'), (∀ x ∈ orth (VS D) (Xplus F ⊔ Xplus F'), x ≠ 0 → 0 < Algebra.trace ℚ D.host.E ((VS D).hT x x)) → ∀ Λ₀ : LV D, Submodule.IsFullLattice D.host.E Λ₀ → {h | h ∈ H0 F F' ∧ Formalism.HermitianLatticesTheory.gmap h Λ₀ = Λ₀}.Finite := by
  intro D T T' F F' hpos Λ₀ hΛ
  refine (finite_of_fix (VS D).hT (Xplus F ⊔ Xplus F') hpos Λ₀ hΛ).subset ?_
  rintro h ⟨⟨hiso, hF, hF'⟩, hlat⟩
  refine ⟨hiso, ?_, hlat⟩
  have key : ∀ {T0 : D.host.E} (G : LFlag (D.sp.Y 0) D.R.rS T0), (∀ a, h (frame G a) = frame G a) →
      Xplus G ≤ LinearMap.ker ((h : (VS D).V →ₗ[D.host.E] (VS D).V) - LinearMap.id) := by
    intro T0 G hG
    have he : ∀ i, h (G.fl.e i) = G.fl.e i := fun i => by
      have := hG (Fin.castSucc i)
      simpa [frame, FlagG.fvec] using this
    have hz : h G.fl.z = G.fl.z := by
      have := hG (Fin.last _)
      simpa [frame, FlagG.fvec] using this
    show Submodule.span D.host.E (Set.range G.fl.e) ⊔ Submodule.span D.host.E {G.fl.z} ≤ _
    refine sup_le (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_)
    · rintro _ ⟨i, rfl⟩
      simp [he i]
    · intro x hx
      rw [Set.mem_singleton_iff] at hx
      subst hx
      simp [hz]
  intro u hu
  have := (sup_le (key F hF) (key F' hF')) hu
  rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] at this
  exact this

end GlobalTheory.StabFin
end
end

section

open scoped Classical ENNReal Pointwise
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Unfold.RowFrame

theorem one_mem_ddS_zpow (D : D7) (n : ℕ) :
    (1 : D.host.E) ∈ (ddS D ^ (-(n : ℤ)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) := by
  have hI0 : ddS D ≠ 0 := by
    unfold ddS
    rw [Ne, FractionalIdeal.coeIdeal_eq_zero]
    rw [Ideal.map_eq_bot_iff_of_injective]
    · exact differentIdeal_ne_bot
    · exact FaithfulSMul.algebraMap_injective _ _
  have hI1 : ddS D ≤ 1 := FractionalIdeal.coeIdeal_le_one
  have hJ0 : ddS D ^ n ≠ 0 := pow_ne_zero _ hI0
  have hJ1 : ddS D ^ n ≤ 1 := pow_le_one' hI1 n
  rw [zpow_neg, zpow_natCast]
  have h1 : (1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) ≤ (ddS D ^ n)⁻¹ := by
    calc (1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) = ddS D ^ n * (ddS D ^ n)⁻¹ :=
          (mul_inv_cancel₀ hJ0).symm
      _ ≤ 1 * (ddS D ^ n)⁻¹ := by gcongr
      _ = (ddS D ^ n)⁻¹ := one_mul _
  exact h1 ((FractionalIdeal.mem_one_iff _).2 ⟨1, map_one _⟩)

theorem frame_mem (D : D7) {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (Λ : LV D) :
    IsRowLat D F0 Λ → ∀ a, frame (lf D F0) a ∈ Λ := by
  rintro ⟨-, ⟨-, -, hlift, -⟩, hX⟩ a
  refine Fin.lastCases ?_ (fun i => ?_) a
  · have e : frame (lf D F0) (Fin.last D.R.rS) = (lf D F0).fl.z := by simp [frame, FlagG.fvec]
    rw [e]
    exact hlift.1
  · have e : frame (lf D F0) i.castSucc = F0.e i := by simp [frame, FlagG.fvec]
    rw [e]
    have hmem : F0.e i ∈ XS D F0 := by
      apply Submodule.subset_span
      refine ⟨i, 1, ?_, (one_smul _ _).symm⟩
      have hk : (-((D.R.rS : ℤ) - ((i : ℕ) : ℤ))) = -(((D.R.rS - (i : ℕ) : ℕ)) : ℤ) := by
        rw [Nat.cast_sub i.isLt.le]
      rw [hk]
      exact one_mem_ddS_zpow D _
    rw [← hX] at hmem
    exact hmem.1

end GlobalTheory.Unfold.RowFrame
end

section

open scoped Classical ENNReal Pointwise
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open ValuativeRel

namespace GlobalTheory.LocCong



theorem qsmul_latP_le_gS : ∀ (D : D7) (Z : LocDat D) (P : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.E)), ((_root_.Formalism.MainNotions.S.Lat.gS D : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal → ∃ sg : Loc.SplitG (Z.M (below D P)).L, (Z.M (below D P)).split = some sg ∧ ∀ (Λ : LV D) (v : Vp D (below D P)), v ∈ (locH Z (below D P)).smulLat (algebraMap (D.s.atP (below D P)).Fp (D.s.atP (below D P)).Ep (sg.q : (D.s.atP (below D P)).Fp)) (lattice₂ D Z.M (below D P) Λ) → v ∈ lattice₂ D Z.M (below D P) (Ideal.span {((_root_.Formalism.MainNotions.S.Lat.gS D : ℕ) : 𝓞 D.host.E)} • Λ) := by
  intro D Z P hP
  set p : PlF D := below D P with hp
  have hmem : ∀ n : ℕ, ((n : 𝓞 D.host.F) ∈ p.asIdeal ↔ ((n : 𝓞 D.host.E)) ∈ P.asIdeal) := by
    intro n
    show (n : 𝓞 D.host.F) ∈ Ideal.comap _ P.asIdeal ↔ _
    rw [Ideal.mem_comap, map_natCast]
  have hg : ∃ i, ((D.host.g i : ℕ) : 𝓞 D.host.F) ∈ p.asIdeal := by
    have h1 : ((_root_.Formalism.MainNotions.S.Lat.gS D : ℕ) : 𝓞 D.host.F) ∈ p.asIdeal := (hmem _).2 hP
    simp only [_root_.Formalism.MainNotions.S.Lat.gS, Nat.cast_mul] at h1
    rcases p.isPrime.mem_or_mem h1 with h | h
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩
  obtain ⟨i, hi⟩ := hg
  have hchar : Loc.resChar p = D.host.g i := by
    have hz : ((D.host.g i : ℕ) : 𝓞 D.host.F ⧸ p.asIdeal) = 0 := by
      rw [← map_natCast (Ideal.Quotient.mk p.asIdeal), Ideal.Quotient.eq_zero_iff_mem]
      exact hi
    have hd : ringChar (𝓞 D.host.F ⧸ p.asIdeal) ∣ D.host.g i := ringChar.dvd hz
    exact (Nat.prime_dvd_prime_iff_eq (D.s.atP p).ellPrime.out (D.host.g_prime i)).1 hd
  obtain ⟨j, hne, hgg⟩ : ∃ j : Fin 2, D.host.g i ≠ D.host.g j ∧ _root_.Formalism.MainNotions.S.Lat.gS D = D.host.g i * D.host.g j := by
    fin_cases i
    · exact ⟨1, D.host.g_ne, rfl⟩
    · exact ⟨0, D.host.g_ne.symm, by simp [_root_.Formalism.MainNotions.S.Lat.gS, mul_comm]⟩
  have hsome : (D.s.atP p).split.isSome := (D.s_split p).2 (by
    rw [hchar]; fin_cases i <;> simp)
  obtain ⟨sg0, hsg0⟩ := Option.isSome_iff_exists.1 hsome
  have hag := (Z.agree p).2.2.2.2.2
  rcases hZs : (Z.M p).split with _ | sg
  · rw [hZs, hsg0] at hag; exact hag.elim
  rw [hZs, hsg0] at hag
  refine ⟨sg, rfl, ?_⟩
  have hq : ((sg.q : 𝒪[(D.s.atP p).Fp]) : (D.s.atP p).Fp) = ((D.host.g i : ℕ) : (D.s.atP p).Fp) := by
    rw [hag.2, sg0.q_eq, hchar]
  have hqO : (sg.q : 𝒪[(D.s.atP p).Fp]) = ((D.host.g i : ℕ) : 𝒪[(D.s.atP p).Fp]) := by
    apply Subtype.ext; rw [hq]; push_cast; rfl
  have hcop : Nat.Coprime (D.host.g i) (D.host.g j) :=
    (Nat.coprime_primes (D.host.g_prime i) (D.host.g_prime j)).2 hne
  have hbez : (1 : ℤ) = (D.host.g i : ℤ) * Int.gcdA (D.host.g i) (D.host.g j) +
      (D.host.g j : ℤ) * Int.gcdB (D.host.g i) (D.host.g j) := by
    have := Int.gcd_eq_gcd_ab (D.host.g i : ℤ) (D.host.g j : ℤ)
    rw [Int.gcd_natCast_natCast, hcop.gcd_eq_one] at this
    exact_mod_cast this
  have hunit : IsUnit ((D.host.g j : ℕ) : 𝒪[(D.s.atP p).Fp]) := by
    have hqn : ((D.host.g i : ℕ) : 𝒪[(D.s.atP p).Fp]) ∈ IsLocalRing.maximalIdeal 𝒪[(D.s.atP p).Fp] := by
      rw [← hqO]; exact sg.q_irr.not_isUnit
    have h1 : IsUnit (1 - ((D.host.g i : ℕ) : 𝒪[(D.s.atP p).Fp]) *
        (Int.gcdA (D.host.g i) (D.host.g j) : 𝒪[(D.s.atP p).Fp])) :=
      IsLocalRing.isUnit_one_sub_self_of_mem_nonunits _ (Ideal.mul_mem_right _ _ hqn)
    have h2 : (1 : 𝒪[(D.s.atP p).Fp]) - ((D.host.g i : ℕ) : 𝒪[(D.s.atP p).Fp]) *
        (Int.gcdA (D.host.g i) (D.host.g j) : 𝒪[(D.s.atP p).Fp]) =
        ((D.host.g j : ℕ) : 𝒪[(D.s.atP p).Fp]) * (Int.gcdB (D.host.g i) (D.host.g j) : 𝒪[(D.s.atP p).Fp]) := by
      have := congrArg (Int.cast : ℤ → 𝒪[(D.s.atP p).Fp]) hbez
      push_cast at this
      rw [this]; ring
    rw [h2] at h1
    exact isUnit_of_mul_isUnit_left h1
  obtain ⟨w, hw⟩ : ∃ w : 𝒪[(D.s.atP p).Fp], (w : (D.s.atP p).Fp) * ((D.host.g j : ℕ) : (D.s.atP p).Fp) = 1 := by
    refine ⟨((hunit.unit⁻¹ : (𝒪[(D.s.atP p).Fp])ˣ) : 𝒪[(D.s.atP p).Fp]), ?_⟩
    have h1 : ((hunit.unit⁻¹ : (𝒪[(D.s.atP p).Fp])ˣ) : 𝒪[(D.s.atP p).Fp]) * ((D.host.g j : ℕ) : 𝒪[(D.s.atP p).Fp]) = 1 := by
      have := hunit.unit.inv_mul
      rwa [IsUnit.unit_spec] at this
    have h2 := congrArg Subtype.val h1
    exact_mod_cast h2
  have hwO : algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (w : (D.s.atP p).Fp) ∈ (Z.M p).L.O := by
    rw [(Z.agree p).2.2.2.1, (D.s.atP p).O_def]
    exact isIntegral_algebraMap
  have hsc : algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (sg.q : (D.s.atP p).Fp) =
      algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (w : (D.s.atP p).Fp) * ((_root_.Formalism.MainNotions.S.Lat.gS D : ℕ) : (D.s.atP p).Ep) := by
    rw [← map_natCast (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep), ← map_mul, hq, hgg]
    congr 1
    push_cast
    calc ((D.host.g i : ℕ) : (D.s.atP p).Fp) = ((D.host.g i : ℕ) : (D.s.atP p).Fp) * ((w : (D.s.atP p).Fp) * ((D.host.g j : ℕ) : (D.s.atP p).Fp)) := by rw [hw, mul_one]
      _ = _ := by ring
  intro Λ v hv
  unfold Loc.HermSp.smulLat at hv
  refine (Submodule.span_le.2 ?_) hv
  rintro _ ⟨y, hy, rfl⟩
  simp only [SetLike.mem_coe]
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨x, hx, rfl⟩ := hy
    rw [hsc, mul_smul]
    have e : ((_root_.Formalism.MainNotions.S.Lat.gS D : ℕ) : (D.s.atP p).Ep) • baseChange₂ D p x = baseChange₂ D p (((_root_.Formalism.MainNotions.S.Lat.gS D : ℕ) : 𝓞 D.host.E) • x) := by
      rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul, map_nsmul]
    rw [e]
    exact (lattice₂ D Z.M p _).smul_mem (⟨_, hwO⟩ : (Z.M p).L.O)
      (Submodule.subset_span ⟨_, Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) hx, rfl⟩)
  | zero => rw [smul_zero]; exact zero_mem _
  | add a b _ _ ha hb => rw [smul_add]; exact add_mem ha hb
  | smul o y _ hy =>
    have e : algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (sg.q : (D.s.atP p).Fp) • (o • y) =
        o • (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (sg.q : (D.s.atP p).Fp) • y) := by
      show _ • ((o : (D.s.atP p).Ep) • y) = (o : (D.s.atP p).Ep) • _
      rw [smul_smul, smul_smul, mul_comm]
    rw [e]; exact Submodule.smul_mem _ _ hy

end GlobalTheory.LocCong
end

section

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.UnipRight

theorem Xflag_eq_Xsp {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T : E}
    (F : LFlag S r T) {j : ℕ} (hj : r ≤ j) : Xflag F j = Xsp F := by
  show Submodule.span E (F.fl.e '' {i | i.1 < j}) = Submodule.span E (Set.range F.fl.e)
  congr 1
  ext v
  simp only [Set.mem_image, Set.mem_setOf_eq, Set.mem_range]
  exact ⟨fun ⟨i, _, h⟩ => ⟨i, h⟩, fun ⟨i, h⟩ => ⟨i, lt_of_lt_of_le i.2 hj, h⟩⟩

theorem map_Xsp_NRat {D : D7} {T : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T) (n : GV D) (hn : n ∈ NRat F) :
    (Xsp F).map (n : (VS D).V →ₗ[D.host.E] (VS D).V) = Xsp F := by
  have hle : (Xsp F).map (n : (VS D).V →ₗ[D.host.E] (VS D).V) ≤ Xsp F := by
    rintro _ ⟨x, hx, rfl⟩
    have h1 : x ∈ Xflag F (D.R.rS + 1) := by rw [Xflag_eq_Xsp F (by omega)]; exact hx
    have h2 := hn.2.1 D.R.rS x h1
    rw [Xflag_eq_Xsp F le_rfl] at h2
    have := (Xsp F).add_mem h2 hx
    simpa using this
  haveI : FiniteDimensional D.host.E (Xsp F) :=
    FiniteDimensional.span_of_finite _ (Set.finite_range _)
  exact Submodule.eq_of_le_of_finrank_eq hle
    (LinearEquiv.finrank_map_eq n (Xsp F))

theorem Xsp_mapLF' {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T : E}
    (γ : S.V ≃ₗ[E] S.V) (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom S.hT) (F : LFlag S r T) :
    Xsp (mapLF γ F) = (Xsp F).map (γ : S.V →ₗ[E] S.V) := by
  unfold mapLF
  rw [dite_eq_left hγ]
  show Submodule.span E (Set.range fun a => γ (F.fl.e a)) =
    (Submodule.span E (Set.range F.fl.e)).map (γ : S.V →ₗ[E] S.V)
  rw [Submodule.map_span, ← Set.range_comp]
  rfl

theorem unip_right : ∀ (D : D7) (T' : D.host.E) (F' : LFlag (D.sp.Y 0) D.R.rS T') (γ₁ γ₂ m n' : GV D),
    γ₁ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT → m ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT → n' ∈ NRat F' → γ₂ = m * γ₁ * n' →
      ∀ x' ∈ orth (VS D) (Xsp (mapLF γ₁ F')), m x' - (γ₂ * γ₁⁻¹) x' ∈ Xsp (mapLF γ₂ F') := by
  intro D T' F' γ₁ γ₂ m n' h1 hm hn hγ x' hx'
  have h2 : γ₂ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := by
    rw [hγ]; exact (Formalism.HermitianLatticesTheory.isom _).mul_mem ((Formalism.HermitianLatticesTheory.isom _).mul_mem hm h1) hn.1
  set y := γ₁.symm x' with hy
  have hyo : y ∈ orth (VS D) (Xsp F') := by
    simp only [orth, Submodule.mem_iInf, LinearMap.mem_ker] at hx' ⊢
    intro z hz
    have hz' : γ₁ z ∈ Xsp (mapLF γ₁ F') := by
      rw [Xsp_mapLF' γ₁ h1]; exact ⟨z, hz, rfl⟩
    have := hx' (γ₁ z) hz'
    rw [← h1 z y, hy]
    simpa using this
  have hd : n' y - y ∈ Xsp F' := hn.2.2 y hyo
  have hd' : y - n' y ∈ Xsp F' := by
    have := (Xsp F').neg_mem hd; simpa using this
  rw [← map_Xsp_NRat F' n' hn] at hd'
  obtain ⟨w, hw, hwe⟩ := hd'
  rw [Xsp_mapLF' γ₂ h2]
  refine ⟨w, hw, ?_⟩
  have hx'y : x' = γ₁ y := by simp [hy]
  show γ₂ w = m x' - (γ₂ * γ₁⁻¹) x'
  rw [hγ, hx'y]
  simp only [LinearEquiv.mul_apply]
  have hinv : γ₁⁻¹ (γ₁ y) = y := by
    show γ₁.symm (γ₁ y) = y
    simp
  have hwe' : n' w = y - n' y := hwe
  rw [hinv, hwe', map_sub, map_sub]

end GlobalTheory.UnipRight
end
end

section

open scoped Classical ENNReal Pointwise
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.LatticeGluingRadicals
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.gluedLattices_stable_under_vectorStabilizer : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (M₀ : Submodule (𝓞 D.host.E) (GlobalTheory.RowsOrb.Ub X u)) (ψ : Submodule (𝓞 D.host.E) (GlobalTheory.RowsOrb.Ub X u) → ℝ≥0∞), (∀ (s : Formalism.HermitianLatticesTheory.isom (GlobalTheory.RowsOrb.hU X u)) (M : Submodule (𝓞 D.host.E) (GlobalTheory.RowsOrb.Ub X u)), ψ (s • M) = ψ M) → GlobalTheory.Mass.Stable (GlobalTheory.RowsOrb.Gz X u) {L : Submodule (𝓞 D.host.E) (GlobalTheory.RowsOrb.Wb X) | Submodule.IsLattice D.host.E L ∧ Formalism.HermitianLatticesTheory.IsUnimodular (GlobalTheory.RowsOrb.hb X) L ∧ (∀ t : D.host.E, t • GlobalTheory.RowsOrb.zb X u ∈ L ↔ t ∈ (1 : Submodule (𝓞 D.host.E) D.host.E)) ∧ GlobalTheory.Mass.latIn (GlobalTheory.RowsOrb.Ub X u) L ∈ Formalism.HermitianLatticesTheory.genus (GlobalTheory.RowsOrb.hU X u) M₀} ∧ ∀ (g : GlobalTheory.RowsOrb.Gz X u) (L : Submodule (𝓞 D.host.E) (GlobalTheory.RowsOrb.Wb X)), ψ (GlobalTheory.Mass.latIn (GlobalTheory.RowsOrb.Ub X u) (g • L)) = ψ (GlobalTheory.Mass.latIn (GlobalTheory.RowsOrb.Ub X u) L) := by
  first | exact @GlobalTheory.RowsOrb.StabSet.main | exact GlobalTheory.RowsOrb.StabSet.main | (intros; apply GlobalTheory.RowsOrb.StabSet.main <;> assumption)
end
