module

public import Development.EtaleCohomology.KummerTheory.Bundle004
public import Development.EtaleCohomology.TateTwists.Bundle005
public import Development.EtaleCohomology.TateTwists.Bundle004
public import Development.EtaleCohomology.TateTwists.Bundle007
public import Development.EtaleCohomology.TateTwists.Bundle002
public import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Triangulated.Yoneda
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
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
import Mathlib.Tactic.TypeStar

@[expose] public section

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.KummerTheory.RedKerPf

open LateralTheory.KummerTheory.BockCut

theorem sepLoc {R : Type} [CommRing R] {F : Shv R} {U : Scheme.{0}} (y z : Sec F U)
    (h : Loc U fun V g => Sec.res g y = Sec.res g z) : y = z := by
  obtain ⟨S, hS, hh⟩ := h
  have h1 := (isSheaf_iff_isSheaf_of_type _ _).1
    ((Presheaf.isSheaf_iff_isSheaf_forget _ F.obj (forget (ModuleCat.{1} (ULift.{1} R)))).1 F.property)
  exact (h1 S hS).isSeparatedFor.ext (fun {V} {g} hg => hh V g hg)

theorem locZero {R : Type} [CommRing R] {F : Shv R} {U : Scheme.{0}} (hL : LateralTheory.EtaleFoundations.EtaleLocalPropertyBasicClosure)
    (y : Sec F U) (h : Loc U fun V g => Sec.res g y = 0) : y = 0 := by
  refine sepLoc y 0 (hL.2.1 U _ _ h fun V g hg => ?_)
  rw [hg]; exact (map_zero _).symm

theorem secEmpty {R : Type} [CommRing R] {F : Shv R} {V : Scheme.{0}} [IsEmpty V]
    (hL : LateralTheory.EtaleFoundations.EtaleLocalPropertyBasicClosure) (y : Sec F V) : y = 0 :=
  sepLoc y 0 (hL.2.2.2.2.2.2 V _)

theorem resMap {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (x : Sec F U) :
    Sec.res g (Sec.map φ x) = Sec.map φ (Sec.res g x) :=
  (congrArg (fun f => (ModuleCat.Hom.hom f) x) (φ.hom.naturality g.op)).symm

theorem resNsmul {R : Type} [CommRing R] {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) (n : ℕ) (x : Sec F U) :
    Sec.res g (n • x) = n • Sec.res g x := map_nsmul _ _ _

theorem mapNsmul {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} (n : ℕ) (x : Sec F U) :
    Sec.map φ (n • x) = n • Sec.map φ x := map_nsmul _ _ _

theorem killTw {q : ℕ} {i : ℤ} {U : Scheme.{0}} (x : Sec (tw q i) U) : q • x = 0 := by
  rw [← Nat.cast_smul_eq_nsmul (ULift.{1} (ZMod q))]
  have : ((q : ℕ) : ULift.{1} (ZMod q)) = 0 := by ext; simp
  rw [this, zero_smul]

theorem kill {q : ℕ} {i : ℤ} {U : Scheme.{0}} (x : Sec (TZ q i) U) : q • x = 0 := killTw (i := i) x

theorem mapGen (hT : LateralTheory.EtaleFoundations.EtaleTateTwistSectionsLocallyGenerated) (hP : LateralTheory.EtaleFoundations.PrimitiveRootsOfUnityBasicIdentities)
    (Q e q : ℕ) [NeZero Q] [NeZero q] (hQ : Q = e * q) (i : ℤ) (π : TZ Q i ⟶ TZ q i) (hπ : IsRed Q q i π)
    (V : Scheme.{0}) [Nonempty V] (ζ : Prim Q Γ(V, ⊤)) (c : ℕ) :
    Sec.map π (c • genZ i ζ) = 0 ↔ q ∣ c := by
  obtain ⟨ξ, hξ⟩ := (hP Q Γ(V, ⊤)).2.2.2.2.2 q ⟨e, by rw [hQ, mul_comm]⟩ ζ
  rw [mapNsmul, hπ V ζ ξ hξ]
  constructor
  · intro h; exact (hT q i).2.2.1 V ξ c h
  · rintro ⟨k, rfl⟩
    rw [mul_comm, mul_smul, kill, smul_zero]

theorem eGen (hT : LateralTheory.EtaleFoundations.EtaleTateTwistSectionsLocallyGenerated)
    (Q e q : ℕ) [NeZero Q] (hQ : Q = e * q) (i : ℤ)
    (V : Scheme.{0}) [Nonempty V] (ζ : Prim Q Γ(V, ⊤)) (c : ℕ) :
    e • (c • genZ i ζ) = 0 ↔ q ∣ c := by
  have he : 0 < e := by
    rcases Nat.eq_zero_or_pos e with h | h
    · exact absurd (by rw [hQ, h, zero_mul]) (NeZero.ne Q)
    · exact h
  rw [← mul_smul]
  constructor
  · intro h
    have := (hT Q i).2.2.1 V ζ (e * c) h
    rw [hQ] at this
    exact (Nat.mul_dvd_mul_iff_left he).1 this
  · rintro ⟨k, rfl⟩
    have : e * (q * k) = Q * k := by rw [hQ]; ring
    rw [this, mul_comm, mul_smul, kill, smul_zero]

theorem RedKer_of (hT : LateralTheory.EtaleFoundations.EtaleTateTwistSectionsLocallyGenerated) (hP : LateralTheory.EtaleFoundations.PrimitiveRootsOfUnityBasicIdentities)
    (hL : LateralTheory.EtaleFoundations.EtaleLocalPropertyBasicClosure) : RedKer := by
  intro Q e q _ hQ i π hπ U y
  haveI : NeZero q := ⟨by rintro rfl; exact NeZero.ne Q (by rw [hQ, mul_zero])⟩
  have L := (hT Q i).1 U y

  have key : Sec.map π y = 0 → Loc U fun V g => Sec.res g y = 0 ∨ (Nonempty V ∧ ∃ (ζ : Prim Q Γ(V, ⊤)) (c : ℕ),
      q ∣ c ∧ Sec.res (F := TZ Q i) g y = c • genZ i ζ) ∨ IsEmpty V := by
    intro h0
    refine hL.2.1 U _ _ L fun V g hg => ?_
    rcases hg with hg | ⟨ζ, c, hc⟩
    · exact Or.inl hg
    rcases isEmpty_or_nonempty V with hV | hV
    · exact Or.inr (Or.inr hV)
    refine Or.inr (Or.inl ⟨hV, ζ, c, ?_, hc⟩)
    have h1 : Sec.map π (Sec.res (F := TZ Q i) g y) = 0 := by rw [← resMap, h0]; exact map_zero _
    have hc' : Sec.res (F := TZ Q i) g y = c • genZ i ζ := hc
    rw [hc'] at h1
    exact (mapGen hT hP Q e q hQ i π hπ V ζ c).1 h1
  refine ⟨⟨fun h0 => ?_, fun h0 => ?_⟩, fun h0 => ?_⟩
  · refine locZero hL _ (hL.2.1 U _ _ (key h0) fun V g hg => ?_)
    rw [resNsmul]
    rcases hg with hg | ⟨hV, ζ, c, hc, hg⟩ | hV
    · rw [hg]; exact smul_zero _
    · rw [hg]; exact (eGen hT Q e q hQ i V ζ c).2 hc
    · exact secEmpty hL _
  · refine locZero hL _ (hL.2.1 U _ _ L fun V g hg => ?_)
    rw [resMap]
    rcases hg with hg | ⟨ζ, c, hc⟩
    · have hg' : Sec.res (F := TZ Q i) g y = 0 := hg
      rw [hg']; exact map_zero _
    rcases isEmpty_or_nonempty V with hV | hV
    · exact secEmpty hL _
    have hc' : Sec.res (F := TZ Q i) g y = c • genZ i ζ := hc
    have h1 : e • Sec.res (F := TZ Q i) g y = 0 := by rw [← resNsmul, h0]; exact map_zero _
    rw [hc'] at h1 ⊢
    exact (mapGen hT hP Q e q hQ i π hπ V ζ c).2 ((eGen hT Q e q hQ i V ζ c).1 h1)
  · refine hL.2.1 U _ _ (key h0) fun V g hg => ?_
    rcases hg with hg | ⟨hV, ζ, c, ⟨k, rfl⟩, hg⟩ | hV
    · exact ⟨0, by rw [hg]; exact smul_zero _⟩
    · exact ⟨k • genZ i ζ, by rw [hg, ← mul_smul]⟩
    · exact ⟨0, by rw [smul_zero]; exact (secEmpty hL _).symm⟩

end LateralTheory.KummerTheory.RedKerPf
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.KummerTheory.RedEpiPf
open LateralTheory.KummerTheory.BockCut

theorem res_comp {R : Type} [CommRing R] {F : Shv R} {W V U : Scheme.{0}} (k : W ⟶ V) (g : V ⟶ U)
    (y : Sec F U) : Sec.res (k ≫ g) y = Sec.res k (Sec.res g y) := by
  simp [Sec.res]

theorem sec_TZ_eq_zero {q : ℕ} (hq : q = 1) (i : ℤ) {V : Scheme.{0}} (x : Sec (TZ q i) V) : x = 0 := by
  subst hq
  have : Subsingleton (Sec (tw 1 i) V) := Module.subsingleton (ULift.{1} (ZMod 1)) _
  exact Subsingleton.elim (α := Sec (tw 1 i) V) x 0

theorem RedEpi_of (h_tw : LateralTheory.EtaleFoundations.EtaleTateTwistSectionsLocallyGenerated) (h_pb : LateralTheory.EtaleFoundations.PrimitiveRootsOfUnityBasicIdentities)
    (h_pl : LateralTheory.EtaleFoundations.EtalePrimitiveRootsExistLocally) (h_me : LateralTheory.EtaleFoundations.EtaleSheafMonoEpiSectionCriteria)
    (h_lb : LateralTheory.EtaleFoundations.EtaleLocalPropertyBasicClosure) : LateralTheory.KummerTheory.BockCut.RedEpi := by
  intro l _ c a hac i π hπ
  obtain ⟨hall, hmono, -, -, htrans, -, -⟩ := h_lb
  have hl0 : l ≠ 0 := (Fact.out : l.Prime).ne_zero
  have : NeZero (l ^ a) := ⟨pow_ne_zero _ hl0⟩
  have : NeZero (l ^ c) := ⟨pow_ne_zero _ hl0⟩
  refine ((h_me ℤ π).2.2.1).2 ?_
  intro U y
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · apply hall
    intro V g
    exact ⟨0, (sec_TZ_eq_zero (pow_zero l) i _).trans (sec_TZ_eq_zero (pow_zero l) i _).symm⟩
  · suffices key : ∀ y' : Sec (tw (l ^ a) i) U, Loc U fun V g =>
        ∃ x : Sec (TZ (l ^ c) i) V, Sec.map π x = (Sec.res (F := tw (l ^ a) i) g y' : Sec (tw (l ^ a) i) V) from key y
    clear y
    intro y
    apply htrans
    refine hmono _ _ _ ((h_tw (l ^ a) i).1 U y) ?_
    intro V g hd
    rcases hd with h0 | ⟨ξ, d, hξ⟩
    · apply hall
      intro W k
      refine ⟨0, ?_⟩
      have e1 : Sec.res (F := tw (l ^ a) i) (k ≫ g) y = 0 := by
        rw [res_comp, h0]
        exact map_zero ((tw (l ^ a) i).obj.map k.op).hom
      have e2 : Sec.map π (0 : Sec (TZ (l ^ c) i) W) = 0 := map_zero (π.hom.app (op W)).hom
      exact e2.trans e1.symm
    · have hla : IsUnit ((l : Γ(V, ⊤)) ^ a) := by simpa using ξ.2.1
      have hl : IsUnit (l : Γ(V, ⊤)) := (isUnit_pow_iff ha.ne').1 hla
      have hlc : IsUnit ((l ^ c : ℕ) : Γ(V, ⊤)) := by simpa using hl.pow c
      apply htrans
      refine hmono _ _ _ ((h_pl (l ^ c) V).1 hlc) ?_
      rintro W k ⟨ζ⟩
      obtain ⟨ζ', hζ'⟩ := (h_pb (l ^ c) Γ(W, ⊤)).2.2.2.2.2 (l ^ a) (pow_dvd_pow l hac) ζ
      refine hmono _ _ _ ((h_tw (l ^ a) i).2.1 W ζ' (Sec.res (F := tw (l ^ a) i) k (Sec.res (F := tw (l ^ a) i) g y))) ?_
      rintro W' k' ⟨e, he⟩
      beta_reduce
      refine ⟨e • genZ i (ζ.map k'.appTop.hom), ?_⟩
      have hr : (ζ'.map k'.appTop.hom).1 = (ζ.map k'.appTop.hom).1 ^ (l ^ c / l ^ a) := by
        show k'.appTop.hom ζ'.1 = (k'.appTop.hom ζ.1) ^ _
        rw [hζ', map_pow]
      have e3 : Sec.res (F := tw (l ^ a) i) ((k' ≫ k) ≫ g) y = e • twGen i (ζ'.map k'.appTop.hom) := by
        rw [res_comp, res_comp, he]
      have e4 : Sec.map π (e • genZ i (ζ.map k'.appTop.hom)) = e • genZ i (ζ'.map k'.appTop.hom) :=
        (map_nsmul (π.hom.app (op W')).hom e _).trans (congrArg (fun z => e • z) (hπ W' _ _ hr))
      exact e4.trans e3.symm

end LateralTheory.KummerTheory.RedEpiPf
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.KummerTheory.SemiUniqPf

theorem cpush_homotopy {R : Type} [CommRing R] (K : Cx R) {I J : Cx R} {f g : I ⟶ J} (ho : Homotopy f g) (n : ℤ)
    (x : CohomologyClass K I n) : cpush K f n x = cpush K g n x := by
  obtain ⟨a, rfl⟩ := x.mk_surjective
  rw [cpost_mk, cpost_mk, ← sub_eq_zero, ← CohomologyClass.mk_sub, CohomologyClass.mk_eq_zero_iff,
    mem_coboundaries_iff _ (n - 1) (by omega)]
  refine ⟨a.1.comp (Cochain.ofHomotopy ho) (by omega), ?_⟩
  rw [δ_comp _ _ _ (n + 1) 0 n (by omega) (by omega) (by omega), δ_ofHomotopy, Cocycle.δ_eq_zero]
  ext p q hpq
  simp [zcomp, Cochain.comp_sub]

theorem secMap_comp {R : Type} [CommRing R] {F G M : Shv R} (f : F ⟶ G) (g : G ⟶ M) {U : Scheme.{0}} (a : Sec F U) :
    Sec.map (f ≫ g) a = Sec.map g (Sec.map f a) := rfl

theorem factor (hZ : LateralTheory.KummerTheory.BockCut.ZHom) (hME : LateralTheory.EtaleFoundations.EtaleSheafMonoEpiSectionCriteria) {S : Type} [CommRing S]
    {I : Cx S} {T J : Cx ℤ} (σ : SemiMap I T) (hσ : ∀ (U : Scheme.{0}) (s : ℤ), Function.Bijective (σ.app U s))
    (κ : SemiMap I J) : ∃ u : T ⟶ J, ∀ (U : Scheme.{0}) (s : ℤ) (a : Sec (I.X s) U),
      κ.app U s a = Sec.map (u.f s) (σ.app U s a) := by
  let e : ∀ (U : Scheme.{0}) (s : ℤ), Sec (I.X s) U ≃+ Sec (T.X s) U :=
    fun U s => AddEquiv.ofBijective (σ.app U s) (hσ U s)
  have he : ∀ U s a, e U s a = σ.app U s a := fun _ _ _ => rfl
  have hu : ∀ s, ∃ φ : T.X s ⟶ J.X s, ∀ (U : Scheme.{0}) (b : Sec (T.X s) U),
      Sec.map φ b = κ.app U s ((e U s).symm b) := by
    intro s
    refine hZ _ _ (fun U => (κ.app U s).comp (e U s).symm.toAddMonoidHom) ?_
    intro V U g b
    obtain ⟨a, rfl⟩ := (e U s).surjective b
    simp only [AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom, AddEquiv.symm_apply_apply]
    rw [κ.nat]
    congr 1
    apply (e V s).injective
    rw [AddEquiv.apply_symm_apply, he, he, σ.nat]
  choose φ hφ using hu
  refine ⟨{ f := φ, comm' := ?_ }, ?_⟩
  · intro s t _
    refine (hME ℤ (φ s ≫ J.d s t)).2.2.2 (T.d s t ≫ φ t) ?_
    intro U b
    obtain ⟨a, rfl⟩ := (e U s).surjective b
    rw [secMap_comp, secMap_comp, hφ, AddEquiv.symm_apply_apply, κ.comm, he, σ.comm, hφ, ← he,
      AddEquiv.symm_apply_apply]
  · intro U s a
    show κ.app U s a = Sec.map (φ s) (σ.app U s a)
    rw [hφ, ← he, AddEquiv.symm_apply_apply]

theorem SemiUniq_of (hRR : LateralTheory.KummerTheory.BockCut.RestrRes) (hZ : LateralTheory.KummerTheory.BockCut.ZHom)
    (hOC : LateralTheory.EtaleFoundations.EtaleCochainSemilinearMapCompCompatible) (hEH : LateralTheory.EtaleFoundations.EtaleKInjectiveHomExtendsAlongQuasiIso)
    (hRB : LateralTheory.EtaleFoundations.EtaleInjectiveResolutionBasicProperties) (hME : LateralTheory.EtaleFoundations.EtaleSheafMonoEpiSectionCriteria) :
    LateralTheory.KummerTheory.BockCut.SemiUniq := by
  intro S _ F G ρ ρ' hρ E n x
  obtain ⟨T, σ, ε, hε, hσ, hσε⟩ := hRR ℤ S (Int.castRingHom S) F
  obtain ⟨u, hu⟩ := factor hZ hME σ hσ ρ
  obtain ⟨u', hu'⟩ := factor hZ hME σ hσ ρ'
  obtain ⟨hK, -, hGE, -⟩ := hRB ℤ G
  have heq : ε ≫ u = ε ≫ u' := by
    apply HomologicalComplex.from_single_hom_ext
    refine (hME ℤ _).2.2.2 _ ?_
    intro U b
    let ι := HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 ((restr (Int.castRingHom S)).obj F)
    have hb : b = Sec.map (sglι _) (Sec.map ι.hom b) := by
      rw [← secMap_comp]; exact (congrArg (fun f => Sec.map f b) ι.hom_inv_id).symm
    have h1 := hσε U (Sec.map ι.hom b)
    dsimp only at h1
    rw [hb]
    change Sec.map (u.f 0) (Sec.map (ε.f 0) (Sec.map (sglι _) (Sec.map ι.hom b))) =
      Sec.map (u'.f 0) (Sec.map (ε.f 0) (Sec.map (sglι _) (Sec.map ι.hom b)))
    rw [h1, ← hu, ← hu']
    exact hρ U _
  obtain ⟨ho⟩ := (hEH ℤ _ T (res ℤ G) ε).2 u u' heq
  rw [(hOC S ℤ σ ρ u hu).1 E n x, (hOC S ℤ σ ρ' u' hu').1 E n x]
  exact cpush_homotopy _ ho n _

end LateralTheory.KummerTheory.SemiUniqPf
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.KummerTheory.RedPostPf
open LateralTheory.KummerTheory.BockCut

variable {S R T : Type} [CommRing S] [CommRing R] [CommRing T]

theorem sec_nat {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (a : Sec F U) :
    Sec.res g (Sec.map φ a) = Sec.map φ (Sec.res g a) := by
  have h := φ.hom.naturality g.op
  exact (congrArg (fun f => f.hom a) h).symm

theorem sec_comp {F G M : Shv R} (φ : F ⟶ G) (ψ : G ⟶ M) {U : Scheme.{0}} (a : Sec F U) :
    Sec.map (φ ≫ ψ) a = Sec.map ψ (Sec.map φ a) := rfl

def scomp {I : Cx S} {J : Cx R} {K : Cx T} (ρ : SemiMap I J) (σ : SemiMap J K) : SemiMap I K where
  app U s := (σ.app U s).comp (ρ.app U s)
  nat g s a := by simp only [AddMonoidHom.comp_apply]; rw [σ.nat, ρ.nat]
  comm U s t a := by simp only [AddMonoidHom.comp_apply]; rw [σ.comm, ρ.comm]

def spost {I : Cx S} {J J' : Cx R} (ρ : SemiMap I J) (u : J ⟶ J') : SemiMap I J' where
  app U s := ((u.f s).hom.app (op U)).hom.toAddMonoidHom.comp (ρ.app U s)
  nat g s a := by
    change Sec.res g (Sec.map (u.f s) (ρ.app _ s a)) = Sec.map (u.f s) (ρ.app _ s (Sec.res g a))
    rw [sec_nat, ρ.nat]
  comm U s t a := by
    change Sec.map (J'.d s t) (Sec.map (u.f s) (ρ.app U s a)) = Sec.map (u.f t) (ρ.app U t (Sec.map (I.d s t) a))
    rw [← ρ.comm, ← sec_comp, ← sec_comp, u.comm]

theorem scomp_op (hS : LateralTheory.EtaleFoundations.EtaleCochainSemilinearMapOnClasses) {I : Cx S} {J : Cx R} {K : Cx T} (ρ : SemiMap I J)
    (σ : SemiMap J K) (E : Spc) (n : ℤ) (x : CohomologyClass ((chains S).obj E) I n) :
    (scomp ρ σ).op.app E n x = σ.op.app E n (ρ.op.app E n x) := by
  obtain ⟨α, rfl⟩ := CohomologyClass.mk_surjective x
  obtain ⟨β, hβ⟩ := (hS S R ρ).1 E n α
  obtain ⟨γ, hγ⟩ := (hS R T σ).1 E n β
  rw [(hS S R ρ).2 E n α β hβ, (hS R T σ).2 E n β γ hγ, (hS S T (scomp ρ σ)).2 E n α γ ?_]
  intro p s h U y
  rw [hγ, hβ]
  rfl

end LateralTheory.KummerTheory.RedPostPf

namespace LateralTheory.KummerTheory.RedPostPf
open LateralTheory.KummerTheory.BockCut

variable {S R : Type} [CommRing S] [CommRing R]

def up {F : Shv S} (φ : R →+* S) {U : Scheme.{0}} (a : Sec ((restr φ).obj F) U) : Sec F U := a

theorem up_add {F : Shv S} (φ : R →+* S) {U : Scheme.{0}} (a b : Sec ((restr φ).obj F) U) :
    up φ (a + b) = up φ a + up φ b := rfl

theorem up_res {F : Shv S} (φ : R →+* S) {V U : Scheme.{0}} (g : V ⟶ U) (a : Sec ((restr φ).obj F) U) :
    Sec.res g (up φ a) = up φ (Sec.res g a) := rfl

theorem sec_add {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} (a b : Sec F U) :
    Sec.map φ (a + b) = Sec.map φ a + Sec.map φ b := map_add _ _ _

theorem RedPost_of (hU : SemiUniq) (hE : TwExt) (hZ : ZHom) (hS : LateralTheory.EtaleFoundations.EtaleCochainSemilinearMapOnClasses)
    (hC : LateralTheory.EtaleFoundations.EtaleCochainSemilinearMapCompCompatible) (hR : LateralTheory.EtaleFoundations.EtaleRootsOfUnityReductionMapGenerator) (hX : LateralTheory.EtaleFoundations.EtaleRestrictScalarsResolutionCompatible)
    (hP : LateralTheory.EtaleFoundations.PrimitiveRootsOfUnityBasicIdentities) (hB : LateralTheory.EtaleFoundations.EtaleInjectiveResolutionBasicProperties) : RedPost := by
  intro Q q _ hq i π hπ E n x
  have : NeZero q := ⟨ne_zero_of_dvd_ne_zero (NeZero.ne Q) hq⟩
  let ρ := scomp (redMap Q q i) (restrMap (Int.castRingHom (ZMod q)) (tw q i))
  let r0 := restrMap (Int.castRingHom (ZMod Q)) (tw Q i)
  let ρ' := spost r0 (resMap ℤ π)
  have h1 : restrH (Int.castRingHom (ZMod q)) E (tw q i) n (red Q q E n i x) = ρ.op.app E n x :=
    (scomp_op hS _ _ E n x).symm
  have h2 : HK.post ℤ ((chains ℤ).obj E) π n (restrH (Int.castRingHom (ZMod Q)) E (tw Q i) n x) = ρ'.op.app E n x :=
    ((hC (ZMod Q) ℤ r0 ρ' (resMap ℤ π) (fun _ _ _ => rfl)).1 E n x).symm
  rw [h1, h2]
  obtain ⟨φ1, hφ1⟩ := hZ (TZ Q i) ((res ℤ (TZ q i)).X 0)
    (fun U => AddMonoidHom.mk' (fun a : Sec (TZ Q i) U => ρ.app U 0 (Sec.map (resι _ (tw Q i)) (up _ a)))
      (fun a b => by rw [up_add, sec_add, map_add (f := _)]))
    (fun V U g a => by
      change Sec.res g (ρ.app U 0 (Sec.map (resι _ (tw Q i)) (up _ a))) = ρ.app V 0 (Sec.map (resι _ (tw Q i)) (up _ (Sec.res g a)))
      rw [ρ.nat, sec_nat, up_res])
  obtain ⟨φ2, hφ2⟩ := hZ (TZ Q i) ((res ℤ (TZ q i)).X 0)
    (fun U => AddMonoidHom.mk' (fun a : Sec (TZ Q i) U => ρ'.app U 0 (Sec.map (resι _ (tw Q i)) (up _ a)))
      (fun a b => by rw [up_add, sec_add, map_add (f := _)]))
    (fun V U g a => by
      change Sec.res g (ρ'.app U 0 (Sec.map (resι _ (tw Q i)) (up _ a))) = ρ'.app V 0 (Sec.map (resι _ (tw Q i)) (up _ (Sec.res g a)))
      rw [ρ'.nat, sec_nat, up_res])
  have heq : φ1 = φ2 := by
    refine hE Q i _ φ1 φ2 fun U ζ => ?_
    obtain ⟨ξ, hξ⟩ := (hP Q Γ(U, ⊤)).2.2.2.2.2 q hq ζ
    rw [hφ1, hφ2]
    change (restrMap (Int.castRingHom (ZMod q)) (tw q i)).app U 0 ((redMap Q q i).app U 0 (resGen i ζ)) =
      Sec.map ((resMap ℤ π).f 0) (r0.app U 0 (Sec.map (resι _ (tw Q i)) (twGen i ζ)))
    rw [hR Q q hq i U ζ ξ hξ, hX ℤ (ZMod Q) _ (tw Q i) U (twGen i ζ)]
    change (restrMap (Int.castRingHom (ZMod q)) (tw q i)).app U 0 (Sec.map (resι _ (tw q i)) (twGen i ξ)) = _
    rw [hX ℤ (ZMod q) _ (tw q i) U (twGen i ξ), ← sec_comp, ((hB ℤ (TZ Q i)).2.2.2.2.2.2.2 (TZ q i) π).2, sec_comp]
    exact congrArg (Sec.map (resι ℤ (TZ q i))) (hπ U ζ ξ hξ).symm
  refine hU (ZMod Q) (tw Q i) (TZ q i) ρ ρ' (fun U a => ?_) E n x
  have e1 := hφ1 U a
  have e2 := hφ2 U a
  rw [heq] at e1
  exact e1.symm.trans e2

end LateralTheory.KummerTheory.RedPostPf
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex Pretriangulated GlobalTheory.EtC

namespace LateralTheory.KummerTheory.NatLESPf
open LateralTheory.KummerTheory.BockCut

theorem exact_transport {A B C A' B' C' : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [AddCommGroup A'] [AddCommGroup B'] [AddCommGroup C'] (eA : A ≃+ A') (eB : B ≃+ B') (eC : C ≃+ C')
    (f : A → B) (g : B → C) (f' : A' → B') (g' : B' → C')
    (hf : ∀ x, eB (f x) = f' (eA x)) (hg : ∀ x, eC (g x) = g' (eB x)) (h : Function.Exact f' g') :
    Function.Exact f g := by
  intro y
  constructor
  · intro hy
    have : g' (eB y) = 0 := by rw [← hg, hy, map_zero]
    obtain ⟨x', hx'⟩ := (h (eB y)).1 this
    refine ⟨eA.symm x', eB.injective ?_⟩
    rw [hf, AddEquiv.apply_symm_apply, hx']
  · rintro ⟨x, rfl⟩
    apply eC.injective
    rw [hg, hf, map_zero]
    exact (h _).2 ⟨_, rfl⟩

theorem NatLES_of (hD : DerDict) : NatLES := by
  intro R _ K
  letI := HasDerivedCategory.standard (Shv R)
  obtain ⟨e, he⟩ := hD R K
  let F := preadditiveCoyoneda.obj (op (DerivedCategory.Q.obj K))
  have hpost : ∀ {X Y : Shv R} (φ : X ⟶ Y) (n : ℤ) (x : HK R K X n),
      e Y n (HK.post R K φ n x) = (F.shift n).map ((DerivedCategory.singleFunctor (Shv R) 0).map φ) (e X n x) := by
    intro X Y φ n x
    rw [he]; rfl
  let d : ∀ (S : ShortComplex (Shv R)), S.ShortExact → ∀ n : ℤ, HK R K S.X₃ n →+ HK R K S.X₁ (n + 1) :=
    fun S hS n => (e S.X₁ (n + 1)).symm.toAddMonoidHom.comp
      ((F.homologySequenceδ hS.singleTriangle n (n + 1) rfl).hom.comp (e S.X₃ n).toAddMonoidHom)
  have hd : ∀ (S : ShortComplex (Shv R)) (hS : S.ShortExact) (n : ℤ) (x : HK R K S.X₃ n),
      e S.X₁ (n + 1) (d S hS n x) = F.homologySequenceδ hS.singleTriangle n (n + 1) rfl (e S.X₃ n x) := by
    intro S hS n x
    exact AddEquiv.apply_symm_apply _ _
  refine ⟨d, fun S hS n => ⟨?_, ?_, ?_⟩, ?_⟩
  · have := F.homologySequence_exact₂ _ hS.singleTriangle_distinguished n
    rw [ShortComplex.ab_exact_iff_function_exact] at this
    exact exact_transport (e S.X₁ n) (e S.X₂ n) (e S.X₃ n) _ _ _ _ (hpost _ n) (hpost _ n) this
  · have := F.homologySequence_exact₃ _ hS.singleTriangle_distinguished n (n + 1) rfl
    rw [ShortComplex.ab_exact_iff_function_exact] at this
    exact exact_transport (e S.X₂ n) (e S.X₃ n) (e S.X₁ (n + 1)) _ _ _ _ (hpost _ n) (hd S hS n) this
  · have := F.homologySequence_exact₁ _ hS.singleTriangle_distinguished n (n + 1) rfl
    rw [ShortComplex.ab_exact_iff_function_exact] at this
    exact exact_transport (e S.X₃ n) (e S.X₁ (n + 1)) (e S.X₂ (n + 1)) _ _ _ _ (hd S hS n)
      (hpost _ (n + 1)) this
  · intro S T hS hT φ n x
    apply (e T.X₁ (n + 1)).injective
    rw [hpost, hd, hd, hpost]
    have := F.homologySequenceδ_naturality (φ := ShortComplex.ShortExact.singleTriangle.map hS hT φ) (n₀ := n) (n₁ := n + 1) (h := rfl)
    have h2 := ConcreteCategory.congr_hom this
      (show ((F.shift n).obj hS.singleTriangle.obj₃ : Type _) from e S.X₃ n x)
    exact h2.symm
end NatLESPf
end KummerTheory
end LateralTheory
end
end
