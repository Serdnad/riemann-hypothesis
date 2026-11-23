module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle011
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle008
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle004
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle012
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.Divisibility.Bundle001
import Formalism.LocalToGlobal.IndefiniteForms.IndefSide

@[expose] public section

section

noncomputable section

namespace GlobalTheory.Cut.SelClass

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass GlobalTheory.Cut

theorem length_le_cob_add {R : Type} [CommRing R] {Γ : Type} [Group Γ] [TopologicalSpace Γ]
    {M : Type} [AddCommGroup M] [Module R M] [TopologicalSpace M]
    [IsTopologicalAddGroup M] [ContinuousConstSMul R M] (rho : Representation R Γ M)
    (C : Submodule R (Γ → M)) (hC : C ≤ ReciprocityTheory.Gal.Z1 rho) (S : Submodule R (ReciprocityTheory.Gal.H1 rho))
    (hS : ∀ f (hf : f ∈ C), (Submodule.Quotient.mk ⟨f, hC hf⟩ : ReciprocityTheory.Gal.H1 rho) ∈ S) :
    Module.length R ↥C ≤ Module.length R ↥(C ⊓ ReciprocityTheory.Gal.B1 rho) + Module.length R ↥S := by

  let ψ : ↥C →ₗ[R] ReciprocityTheory.Gal.H1 rho :=
    ((ReciprocityTheory.Gal.B1 rho).comap (ReciprocityTheory.Gal.Z1 rho).subtype).mkQ ∘ₗ Submodule.inclusion hC
  have hker : ∀ x : ↥C, ψ x = 0 → (x : Γ → M) ∈ ReciprocityTheory.Gal.B1 rho := by
    intro x hx
    have h := (Submodule.Quotient.mk_eq_zero _).1 hx
    simpa using h
  have hrange : LinearMap.range ψ ≤ S := by
    rintro _ ⟨x, rfl⟩
    exact hS x.1 x.2
  let K := LinearMap.ker ψ.rangeRestrict
  have hsplit := Module.length_eq_add_of_exact K.subtype ψ.rangeRestrict
    (Submodule.subtype_injective _) ψ.surjective_rangeRestrict
    (LinearMap.exact_subtype_ker_map _)

  let j : ↥K →ₗ[R] ↥(C ⊓ ReciprocityTheory.Gal.B1 rho) :=
    LinearMap.codRestrict (C ⊓ ReciprocityTheory.Gal.B1 rho) (C.subtype ∘ₗ K.subtype) (fun x => by
      refine ⟨x.1.2, hker x.1 ?_⟩
      have hx : ψ.rangeRestrict x.1 = 0 := x.2
      exact congrArg Subtype.val hx)
  have hj : Function.Injective j := by
    intro a b hab
    have h := congrArg Subtype.val hab
    exact Subtype.ext (Subtype.ext h)
  have hK := Module.length_le_of_injective j hj
  have hI := Module.length_le_of_injective (Submodule.inclusion hrange) (Submodule.inclusion_injective hrange)
  rw [hsplit]
  exact add_le_add hK hI




theorem mk_mem_selG {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] (A : Formalism.GaloisCohomology.Places E Ω)
    (l : ℕ) [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [Algebra ℤ_[l] O] [TopologicalSpace O]
    (P : LocPrime l)
    (nb : ∀ w, w ∈ placesOver E l → LocBridge l E Ω (Dec (F := E) (A.1 w)) O)
    (Sig : Set (HeightOneSpectrum (𝓞 E))) {k : ℕ} (M : Formalism.ConjugateSelfDual.G E Ω →* Matrix (Fin k) (Fin k) O)
    (f : ↥(ReciprocityTheory.Gal.Z1 (WKG M)))
    (hl : ∀ w hw, (fun g => Br.phi (nb w hw) k (f.1 (Br.ι (nb w hw) g).1)) ∈
      HfD (P.PD (nb w hw).Kw) (Br.lat (nb w hw) (M.comp (Dec (F := E) (A.1 w)).subtype)))
    (hu : ∀ v, v ∉ placesOver E l → v ∉ Sig → ∀ g ∈ Ine (F := E) (A.1 v), f.1 g = 0) :
    (Submodule.Quotient.mk f : ReciprocityTheory.Gal.H1 (WKG M)) ∈ Br.selG A l P nb Sig M := by
  unfold Br.selG GaloisCohomology.SelAll GaloisCohomology.bkCond Br.LlG Sel
  refine (Submodule.mem_iInf _).2 fun v => ?_
  rw [Submodule.mem_comap]
  dsimp only
  split_ifs with h1 h2 h3
  · unfold Br.bkG
    refine Submodule.mem_map.2 ⟨_, ?_, rfl⟩
    exact hl v h2
  · exact Submodule.mem_top
  · exact Submodule.mem_top
  · have hv : v ∉ placesOver E l := h1
    unfold GaloisCohomology.unrAt H1ur
    rw [LinearMap.mem_ker]
    unfold ReciprocityTheory.Gal.resH1
    rw [Submodule.mapQ_apply, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]

    convert (ReciprocityTheory.Gal.B1 _).zero_mem using 1
    funext g
    exact hu v hv h3 _ g.2




theorem main : ∀ (D : D7) (i : D.nd.Loc) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (C : Submodule (D.nd.O i) (GE D.nd → KOG (D.nd.O i) D.R.r)), C ≤ Z1 (WKG (WpO D.nd i ρ π)) → (∀ f ∈ C, IsFinL i (WpO D.nd i ρ π) f) → (∀ v, v ∉ placesOver D.host.E (D.nd.l i) → v ∉ D.nd.S i → v ∉ D.nd.Q i → resIne i C v = ⊥) → Module.length (D.nd.O i) ↥C ≤ lenCob i (WpO D.nd i ρ π) (C) + Module.length (D.nd.O i) ↥(Br.selPi D.loc D.nbr i ρ π) := by
  intro D i ρ π C hC hfin hine
  unfold lenCob
  refine length_le_cob_add _ C hC _ (fun f hf => ?_)
  unfold Br.selPi
  refine mk_mem_selG D.nd.plOm (D.nd.l i) (D.loc (D.nd.l i)) (D.nbr i) _ (WpO D.nd i ρ π) ⟨f, hC hf⟩ ?_ ?_
  · intro w hw
    exact hfin f hf w hw
  · intro v hv hSig g hg
    have hSv : v ∉ D.nd.S i := fun h => hSig (Or.inl h)
    have hQv : v ∉ D.nd.Q i := fun h => hSig (Or.inr h)

    have hmem : LinearMap.funLeft (D.nd.O i) (KOG (D.nd.O i) D.R.r) Subtype.val f ∈ resIne i C v :=
      Submodule.mem_map_of_mem hf
    rw [hine v hv hSv hQv, Submodule.mem_bot] at hmem
    exact congrFun hmem ⟨g, hg⟩

end GlobalTheory.Cut.SelClass

end
end

section

noncomputable section

namespace GlobalTheory.MirAvg

open Polynomial GlobalTheory.GLq

variable {g : ℕ} [Fact g.Prime]

def mirSet {r : ℕ} (a : Fin r → ZMod g) (b : Bool) (h : Gn g r) : Prop :=
  if b then ∀ x : Fin r → ZMod g, ∃ c : ZMod g, (h : Mt g r).mulVec x - x = c • a
  else ∀ x : Fin r → ZMod g, a ⬝ᵥ x = 0 → (h : Mt g r).mulVec x = x


open Classical in
def mirEl {r : ℕ} (θ : (ZMod g)ˣ →* ℂˣ) (a : Fin r → ZMod g) (b : Bool) : MonoidAlgebra ℂ (Gn g r) :=
  ∑ h : Gn g r, MonoidAlgebra.single h (if mirSet a b h then ((θ (Matrix.GeneralLinearGroup.det h) : ℂˣ) : ℂ) else 0)

def SeriesKillsAvg : Prop :=
  ∀ (g : ℕ) [Fact g.Prime] (L : LabelDatum g) (r : ℕ) (f : (ZMod g)[X]) (θ : (ZMod g)ˣ →* ℂˣ) (c : ZMod g),
    GlobalTheory.GLp.IsCharLab L θ c → ¬ f.IsRoot c → ¬ f.IsRoot c⁻¹ → ∀ (a : Fin r → ZMod g) (b : Bool), a ≠ 0 →
      eSerC L r f * mirEl θ a b = 0

end GlobalTheory.MirAvg
end
end

section

noncomputable section
open Formalism.BasicNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef NumberField IsDedekindDomain GlobalTheory.EtaJoin

namespace GlobalTheory.EtaJoin.SpecProj

theorem le_iSup_of_dichotomy {V ι : Type} [AddCommGroup V] [Module ℂ V] (T : ι → Submodule ℂ V) (A B : Submodule ℂ V)
    (hd : Disjoint A B) (ht : ⨆ P, T P = ⊤) (h : ∀ P, T P ≤ A ∨ T P ≤ B) : A ≤ ⨆ P ∈ {P | T P ≤ A}, T P := by
  intro x hx
  have hle : (⊤ : Submodule ℂ V) ≤ (⨆ P ∈ {P | T P ≤ A}, T P) ⊔ B := by
    rw [← ht]
    refine iSup_le fun P => (h P).elim (fun hP => le_sup_of_le_left ?_) le_sup_of_le_right
    exact le_biSup T (show P ∈ {P | T P ≤ A} from hP)
  obtain ⟨a, ha, b, hb, e⟩ := Submodule.mem_sup.1 (hle (Submodule.mem_top (x := x)))
  have ha' : a ∈ A := (iSup₂_le fun P hP => hP : (⨆ P ∈ {P | T P ≤ A}, T P) ≤ A) ha
  have hb0 : b = 0 := Submodule.disjoint_def.1 hd b (by rw [← add_sub_cancel_left a b, e]; exact A.sub_mem hx ha') hb
  rw [← e, hb0, add_zero]; exact ha

theorem specPr_of_zSpec_typeTie : ∀ (D : D7) (i : D.nd.Loc), ZSpec D i → TypeTie D i → SpecPr D i := by
  intro D i hZ hT
  have hd := (Idx.Z0 D (D.nd.mu i) (D.nd.j i)).orthogonal_disjoint
  have mono : ∀ {Y Y' : Set (D.nd.X i)}, Y ⊆ Y' → D.nd.eigSum i Y ≤ D.nd.eigSum i Y' := fun h => biSup_mono h
  constructor
  · intro y hy
    refine mono ?_ (hT _ y (le_iSup_of_dichotomy _ _ _ hd (D.naut.typeV_top i) (fun P => (hZ P).1) hy))
    rintro x ⟨P, hP, hx⟩
    by_contra hn
    exact D.naut.typeV_ne i P (hd hP (((hZ P).2 x hx).2 hn) |> le_bot_iff.1)
  · intro y hy
    refine mono ?_ (hT _ y (le_iSup_of_dichotomy _ _ _ hd.symm (D.naut.typeV_top i) (fun P => (hZ P).1.symm) hy))
    rintro x ⟨P, hP, hx⟩ hn
    exact D.naut.typeV_ne i P (hd (((hZ P).2 x hx).1 hn) hP |> le_bot_iff.1)

end GlobalTheory.EtaJoin.SpecProj
end
end

section

noncomputable section
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models GlobalTheory.TopSteps GlobalTheory.Present Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped LaurentSeries PowerSeries
namespace GlobalTheory.Present.SumRed

section General
variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n₀ : ℕ}

theorem exists_proj {T T' Z : LocLat G Qp LL O} (f : LatHom T.L Z.L) (g : LatHom T'.L Z.L)
    (hb : Function.Bijective (f.f.coprod g.f))
    (hs : ∀ z ∈ Z.L.T, ∃ x ∈ T.L.T, ∃ y ∈ T'.L.T, z = f.f x + g.f y) :
    ∃ (p : LatHom Z.L T.L) (p' : LatHom Z.L T'.L), latAdd (latComp f p) (latComp g p') = latId Z := by
  let e : (T.V × T'.V) ≃ₗ[LL] Z.V := LinearEquiv.ofBijective _ hb
  have he : ∀ x y, e.symm (f.f x + g.f y) = (x, y) := fun x y => by
    rw [LinearEquiv.symm_apply_eq]; rfl
  have hz : ∀ z, f.f (e.symm z).1 + g.f (e.symm z).2 = z := fun z => e.apply_symm_apply z
  have hρ : ∀ σ z, e.symm (Z.ρ σ z) = (T.ρ σ (e.symm z).1, T'.ρ σ (e.symm z).2) := fun σ z => by
    rw [← he, f.equiv, g.equiv, ← map_add (f := _), hz]
  haveI := T.mtop.toContinuousSMul
  haveI := T'.mtop.toContinuousSMul
  refine ⟨⟨LinearMap.fst LL _ _ ∘ₗ e.symm.toLinearMap, fun σ z => ?_,
      IsModuleTopology.continuous_of_linearMap _, fun z h => ?_⟩,
    ⟨LinearMap.snd LL _ _ ∘ₗ e.symm.toLinearMap, fun σ z => ?_,
      IsModuleTopology.continuous_of_linearMap _, fun z h => ?_⟩, ?_⟩
  · exact congrArg Prod.fst (hρ σ z)
  · obtain ⟨x, hx, y, hy, rfl⟩ := hs z h
    change (e.symm _).1 ∈ _
    rw [he]; exact hx
  · exact congrArg Prod.snd (hρ σ z)
  · obtain ⟨x, hx, y, hy, rfl⟩ := hs z h
    change (e.symm _).2 ∈ _
    rw [he]; exact hy
  · unfold latAdd latId
    congr 1
    exact LinearMap.ext hz

variable (W : LocWach PD LL O v n₀)

theorem map_mem {T Z : LocLat G Qp LL O} (f : LatHom T.L Z.L) (x : ↥(DΔ W T)) :
    W.map f (x : W.DD T) ∈ DΔ W Z := fun δ hδ => by
  rw [← W.map_γ, x.2 δ hδ]

theorem red_sum {k : Type} [Field k] [Algebra O k] {l n : ℕ} {R : RingPG k l} {F : DFun R n G}
    {ι : k⸨X⸩ →ₐ[k] k⸨X⸩} {τ : ZMod n → ZMod n₀} {γ : W.Gam} (p : Pres W F ι τ γ)
    {T T' Z : LocLat G Qp LL O} {A A' C : Ob k G} {q q' r}
    (hq : Onto T A q) (hq' : Onto T' A' q') (hr : Onto Z C r)
    (hT : IsCrys PD T.ρ) (hT' : IsCrys PD T'.ρ) (hZ : IsCrys PD Z.ρ)
    (f : LatHom T.L Z.L) (g : LatHom T'.L Z.L) (a : (Fin A.m → k) →ₗ[k] (Fin C.m → k))
    (b : (Fin A'.m → k) →ₗ[k] (Fin C.m → k)) (hb : Function.Bijective (f.f.coprod g.f))
    (hs : ∀ z ∈ Z.L.T, ∃ x ∈ T.L.T, ∃ y ∈ T'.L.T, z = f.f x + g.f y) (ha : IsHom A C a) (hb' : IsHom A' C b)
    (hfa : ∀ (x : ↥T.L.T) (x' : ↥Z.L.T), (x' : Z.V) = f.f x → r x' = a (q x))
    (hgb : ∀ (x : ↥T'.L.T) (x' : ↥Z.L.T), (x' : Z.V) = g.f x → r x' = b (q' x))
    (N : Lats k n A.m) (N' : Lats k n A'.m) (L : Lats k n C.m)
    (hN : ∀ i y, y ∈ N i ↔ ∃ x : ↥(DΔ W T), (x : W.DD T) ∈ W.N T ∧ p.j T A q i x = y)
    (hN' : ∀ i y, y ∈ N' i ↔ ∃ x : ↥(DΔ W T'), (x : W.DD T') ∈ W.N T' ∧ p.j T' A' q' i x = y)
    (hL : ∀ i y, y ∈ L i ↔ ∃ x : ↥(DΔ W Z), (x : W.DD Z) ∈ W.N Z ∧ p.j Z C r i x = y) (i : ZMod n) :
    L i = F.push A C a N i ⊔ F.push A' C b N' i := by
  obtain ⟨π, π', hπ⟩ := exists_proj f g hb hs
  apply le_antisymm
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := (hL i y).1 hy
    let x₁ : ↥(DΔ W T) := ⟨_, map_mem W π x⟩
    let x₂ : ↥(DΔ W T') := ⟨_, map_mem W π' x⟩
    have hsum : x = ⟨_, map_mem W f x₁⟩ + ⟨_, map_mem W g x₂⟩ := by
      apply Subtype.ext
      have := W.map_id Z x
      rw [← hπ, W.map_latAdd, W.map_comp, W.map_comp] at this
      exact this.symm
    rw [hsum, map_add (f := _), p.j_map T A q Z C r hq hr f a ha hfa i x₁ _ rfl,
      p.j_map T' A' q' Z C r hq' hr g b hb' hgb i x₂ _ rfl]
    exact Submodule.add_mem_sup
      ⟨_, (hN i _).2 ⟨x₁, W.map_N π hZ hT _ hx, rfl⟩, rfl⟩
      ⟨_, (hN' i _).2 ⟨x₂, W.map_N π' hZ hT' _ hx, rfl⟩, rfl⟩
  · refine sup_le ?_ ?_
    · rintro _ ⟨y, hy, rfl⟩
      obtain ⟨x, hx, rfl⟩ := (hN i y).1 hy
      exact (hL i _).2 ⟨⟨_, map_mem W f x⟩, W.map_N f hT hZ _ hx,
        p.j_map T A q Z C r hq hr f a ha hfa i x _ rfl⟩
    · rintro _ ⟨y, hy, rfl⟩
      obtain ⟨x, hx, rfl⟩ := (hN' i y).1 hy
      exact (hL i _).2 ⟨⟨_, map_mem W g x⟩, W.map_N g hT' hZ _ hx,
        p.j_map T' A' q' Z C r hq' hr g b hb' hgb i x _ rfl⟩

end General

theorem reduction_sum : ∀ {l : ℕ} [Fact l.Prime] {P : LocPrime l} (H : LocHW l P) (S : TopSit P) (k : Type) [Field k] [Algebra S.O k] [CharP k l], S.IsRes k → ∀ {R : RingPG k l} (ι : k⸨X⸩ →ₐ[k] k⸨X⸩) (F : DFun R S.n S.G) (τ : ZMod S.n → ZMod (Module.finrank ℚ_[l] ↥(K0 S.K))) (γ : (S.W H).Gam) (p : Pres (S.W H) F ι τ γ), GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.IsCyclotomic R ι → (∀ i, (S.W H).emb (τ i) = S.emb i) → ((S.W H).χΓ γ : S.O) = 1 + (l : S.O) → GlobalTheory.WachUse.QN (S.W H) → ∀ (T : LocLat S.G ℚ_[l] ↥S.LL.1 S.O) (A : Ob k S.G) q (U : ZMod S.n → Multiset ℤ), Onto T A q → KerIs S.Γ.lam q → CrysWith (P.PD S.K) S.emb T.ρ U → ∀ (T' : LocLat S.G ℚ_[l] ↥S.LL.1 S.O) (A' : Ob k S.G) q' (U' : ZMod S.n → Multiset ℤ), Onto T' A' q' → KerIs S.Γ.lam q' → CrysWith (P.PD S.K) S.emb T'.ρ U' → ∀ (Z : LocLat S.G ℚ_[l] ↥S.LL.1 S.O) (C : Ob k S.G) r (V : ZMod S.n → Multiset ℤ), Onto Z C r → KerIs S.Γ.lam r → CrysWith (P.PD S.K) S.emb Z.ρ V → ∀ (f : LatHom T.L Z.L) (g : LatHom T'.L Z.L) (a : (Fin A.m → k) →ₗ[k] (Fin C.m → k)) (b : (Fin A'.m → k) →ₗ[k] (Fin C.m → k)), Function.Bijective (f.f.coprod g.f) → (∀ z ∈ Z.L.T, ∃ x ∈ T.L.T, ∃ y ∈ T'.L.T, z = f.f x + g.f y) → IsHom A C a → IsHom A' C b → (∀ (x : ↥T.L.T) (x' : ↥Z.L.T), (x' : Z.V) = f.f x → r x' = a (q x)) → (∀ (x : ↥T'.L.T) (x' : ↥Z.L.T), (x' : Z.V) = g.f x → r x' = b (q' x)) → ∀ (N : Lats k S.n A.m) (N' : Lats k S.n A'.m) (L : Lats k S.n C.m), (∀ i y, y ∈ N i ↔ ∃ x : ↥(DΔ (S.W H) T), (x : (S.W H).DD T) ∈ (S.W H).N T ∧ p.j T A q i x = y) → (∀ i y, y ∈ N' i ↔ ∃ x : ↥(DΔ (S.W H) T'), (x : (S.W H).DD T') ∈ (S.W H).N T' ∧ p.j T' A' q' i x = y) → (∀ i y, y ∈ L i ↔ ∃ x : ↥(DΔ (S.W H) Z), (x : (S.W H).DD Z) ∈ (S.W H).N Z ∧ p.j Z C r i x = y) → ∀ i, L i = F.push A C a N i ⊔ F.push A' C b N' i := by
  intro l _ P H S k _ _ _ _ R ι F τ γ p _ _ _ _ T A q U hq _ hT T' A' q' U' hq' _ hT' Z C r V hr _ hZ
    f g a b hb hs ha hb' hfa hgb N N' L hN hN' hL i
  exact red_sum (S.W H) p hq hq' hr hT.1 hT'.1 hZ.1 f g a b hb hs ha hb' hfa hgb N N' L hN hN' hL i

end GlobalTheory.Present.SumRed
end
end

section

open GlobalTheory.GLq GlobalTheory.GLp Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical

namespace GlobalTheory.GLp

theorem exists_upper_mul_inc : ∀ (g : ℕ) [Fact g.Prime] (n : ℕ) (h : GL (Fin n) ℚ_[g]), ∃ (p : GL (Fin n) ℚ_[g]) (k : GL (Fin n) ℤ_[g]), (∀ i j : Fin n, j < i → (p : Matrix (Fin n) (Fin n) ℚ_[g]) i j = 0) ∧ h = p * inc g n k := by
  intro g hg n h
  have hdet : ((h⁻¹ : GL (Fin n) ℚ_[g]) : Matrix (Fin n) (Fin n) ℚ_[g]).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).mp (Units.isUnit _)).ne_zero
  obtain ⟨k, U, hk, hU, -, hA⟩ := Formalism.L2.Pj.iwasawa (V := ℤ_[g]) _ hdet

  have hUdet : IsUnit U.det := by
    rw [hA, Matrix.det_mul] at hdet
    exact isUnit_iff_ne_zero.mpr (right_ne_zero_of_mul hdet)
  let K : GL (Fin n) ℤ_[g] := ((Matrix.isUnit_iff_isUnit_det k).mpr hk).unit
  have hinc : ((inc g n K : GL (Fin n) ℚ_[g]) : Matrix (Fin n) (Fin n) ℚ_[g]) =
      k.map (algebraMap ℤ_[g] ℚ_[g]) := rfl
  refine ⟨h * inc g n K, K⁻¹, ?_, ?_⟩
  · intro i j hij
    have e1 : ((h * inc g n K : GL (Fin n) ℚ_[g]) : Matrix (Fin n) (Fin n) ℚ_[g]) = U⁻¹ := by
      rw [Units.val_mul, hinc]
      calc (h : Matrix (Fin n) (Fin n) ℚ_[g]) * k.map (algebraMap ℤ_[g] ℚ_[g])
          = (h : Matrix (Fin n) (Fin n) ℚ_[g]) * (k.map (algebraMap ℤ_[g] ℚ_[g]) * U) * U⁻¹ := by
            rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_nonsing_inv U hUdet, Matrix.mul_one]
        _ = U⁻¹ := by rw [← hA, Units.mul_inv, Matrix.one_mul]
    rw [e1]
    haveI := Matrix.invertibleOfIsUnitDet U hUdet
    exact Matrix.blockTriangular_inv_of_blockTriangular hU hij
  · rw [map_inv, mul_inv_cancel_right]

end GlobalTheory.GLp
end

section

open GlobalTheory.TripleGal Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.TripleGal.HkFrobProof

theorem eval_charpolyRev_eq {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (z : ℂ) :
    M.charpolyRev.eval z = (1 - z • M).det := by
  rw [Matrix.charpolyRev, ← coe_evalRingHom, RingHom.map_det]
  congr 1
  ext a b
  by_cases h : a = b <;> simp [h] <;> ring

theorem coeff_charpolyRev_map {n : ℕ} {R : Type} [CommRing R] (f : R →+* ℂ) (M : Matrix (Fin n) (Fin n) R) (k : ℕ) :
    f (M.charpolyRev.coeff k) = (M.map f).charpolyRev.coeff k := by
  rw [← Polynomial.coeff_map]
  apply congrArg (fun p : ℂ[X] => p.coeff k)
  rw [Matrix.charpolyRev, Matrix.charpolyRev, ← coe_mapRingHom, RingHom.map_det]
  congr 1
  ext a b : 1
  by_cases h : a = b <;> simp [h]

theorem charpolyRev_smul_inv {n : ℕ} (M A : Matrix (Fin n) (Fin n) ℂ) (h : M * A = 1) (β : Multiset ℂ)
    (hβ : (0 : ℂ) ∉ β) (hA : A.charpoly = (β.map fun a => (X : ℂ[X]) - C a).prod) (c : ℂ) :
    (c • M).charpolyRev = (β.map fun a => (1 : ℂ[X]) - C (c * a⁻¹) * X).prod := by
  have ev : ∀ y : ℂ, (y • (1 : Matrix (Fin n) (Fin n) ℂ) - A).det = (β.map fun a => y - a).prod := by
    intro y
    have := congrArg (Polynomial.eval y) hA
    rw [Matrix.eval_charpoly, eval_multiset_prod, Multiset.map_map, Matrix.scalar_apply,
      ← Matrix.smul_one_eq_diagonal] at this
    simpa using this
  apply Polynomial.funext
  intro z
  rw [eval_charpolyRev_eq, eval_multiset_prod, Multiset.map_map]
  have h0 := ev 0
  have h1 := ev (z * c)
  have hne : (β.map fun a => (0 : ℂ) - a).prod ≠ 0 := by
    apply Multiset.prod_ne_zero
    intro hm
    obtain ⟨a, ha, ha0⟩ := Multiset.mem_map.1 hm
    have : a = 0 := by simpa using ha0
    exact hβ (this ▸ ha)
  apply mul_right_cancel₀ hne
  rw [← Multiset.prod_map_mul]
  conv_lhs => rw [← h0, ← Matrix.det_mul]
  have e : (1 - z • c • M) * ((0 : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) - A) = (z * c) • 1 - A := by
    rw [zero_smul, zero_sub, mul_neg, sub_mul, one_mul, smul_smul, Matrix.smul_mul, h, neg_sub]
  rw [e, h1]
  congr 1
  apply Multiset.map_congr rfl
  intro a ha
  have ha0 : a ≠ 0 := fun h => hβ (h ▸ ha)
  simp only [Function.comp, eval_sub, eval_one, eval_mul, eval_C, eval_X]
  field_simp
  ring

theorem rd_injective {D : D7} (i : D.ntw.Tw) (ι : FractionRing (D.ntw.O0 i) →+* ℂ) :
    Function.Injective (rd i ι) :=
  ι.injective.comp (IsFractionRing.injective (D.ntw.O0 i) (FractionRing (D.ntw.O0 i)))

end GlobalTheory.TripleGal.HkFrobProof
end

section

noncomputable section

open GlobalTheory.TripleGal Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain

namespace GlobalTheory.ReadEmbEx

theorem exists_read {l : ℕ} [Fact l.Prime] {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω] {Gw : Subgroup (Ω ≃ₐ[E] Ω)}
    {O : Type} [CommRing O] [IsDomain O] [Algebra ℤ_[l] O] [TopologicalSpace O] (B : LocBridge l E Ω Gw O)
    (ι : FractionRing O →+* ℂ) :
    ∃ φ : ↥B.LL.1 →+* ℂ, ∀ a : O, φ (B.toLL a) = ι (algebraMap O (FractionRing O) a) := by
  have hinj : Function.Injective B.toLL := fun _ _ h => B.eO.injective (Subtype.ext h)
  let f : FractionRing O →+* ↥B.LL.1 := IsFractionRing.lift (g := B.toLL) hinj
  have hf : ∀ a : O, f (algebraMap O (FractionRing O) a) = B.toLL a := fun a =>
    IsFractionRing.lift_algebraMap _ a
  have hb : Function.Bijective f := by
    refine ⟨f.injective, fun y => ?_⟩
    have hint (x : Om l) : IsIntegral ℤ_[l] x ↔ ‖x‖ ≤ 1 := by
      have hx : IsIntegral ℚ_[l] x := Algebra.IsIntegral.isIntegral x
      rw [← PadicAlgCl.spectralNorm_eq, spectralNorm, spectralValue_le_one_iff (minpoly.monic hx)]
      constructor
      · intro h n
        rw [minpoly.isIntegrallyClosed_eq_field_fractions' ℚ_[l] h, Polynomial.coeff_map]
        exact ((minpoly ℤ_[l] x).coeff n).2
      · intro h
        have hl : minpoly ℚ_[l] x ∈ Polynomial.lifts (algebraMap ℤ_[l] ℚ_[l]) := by
          rw [Polynomial.lifts_iff_coeff_lifts]
          exact fun n => ⟨⟨_, h n⟩, rfl⟩
        obtain ⟨q, hq, -, hqm⟩ := Polynomial.lifts_and_degree_eq_and_monic hl (minpoly.monic hx)
        refine ⟨q, hqm, ?_⟩
        rw [← Polynomial.aeval_def, ← Polynomial.aeval_map_algebraMap ℚ_[l], hq, minpoly.aeval]
    have hmem (x : ↥B.LL.1) : x ∈ OL B.LL ↔ ‖(x : Om l)‖ ≤ 1 := by
      rw [← hint, OL, mem_integralClosure_iff]
      exact (isIntegral_algHom_iff (B.LL.1.val.restrictScalars ℤ_[l]) B.LL.1.val.toRingHom.injective).symm
    have hnorm (x : ↥B.LL.1) : ‖(x : Om l)‖ ≤ 1 → ∃ n : O, x = B.toLL n := by
      intro hx
      refine ⟨B.eO.symm ⟨x, (hmem x).2 hx⟩, ?_⟩
      simp [LocBridge.toLL]
    have hfrac (y : ↥B.LL.1) : ∃ n d : O, d ≠ 0 ∧ B.toLL d * y = B.toLL n := by
      by_cases h : ‖(y : Om l)‖ ≤ 1
      · obtain ⟨n, hn⟩ := hnorm y h
        refine ⟨n, 1, fun h1 => ?_, by simp [hn]⟩
        have := congrArg B.toLL h1
        simp at this
      · have hy : y ≠ 0 := by
          rintro rfl
          simp at h
        have h' : ‖((y⁻¹ : ↥B.LL.1) : Om l)‖ ≤ 1 := by
          rw [IntermediateField.coe_inv, norm_inv]
          exact inv_le_one_of_one_le₀ (not_le.1 h).le
        obtain ⟨d, hd⟩ := hnorm _ h'
        refine ⟨1, d, fun h1 => ?_, by rw [← hd, map_one, inv_mul_cancel₀ hy]⟩
        rw [h1, map_zero] at hd
        exact hy (inv_eq_zero.1 hd)
    obtain ⟨n, d, hd, e⟩ := hfrac y
    have hd' : B.toLL d ≠ 0 := fun h0 => hd (hinj (h0.trans (map_zero _).symm))
    refine ⟨algebraMap O _ n / algebraMap O _ d, ?_⟩
    rw [map_div₀, hf, hf, ← e, mul_div_cancel_left₀ _ hd']
  let e := RingEquiv.ofBijective f hb
  refine ⟨ι.comp e.symm.toRingHom, fun a => ?_⟩
  rw [← hf]
  exact congrArg ι (e.symm_apply_apply _)

theorem exists_readEmb : ∀ (D : D7) (bkP : BlochKatoReduction.BK D) (i : D.ntw.Tw) (ι : FractionRing (D.ntw.O0 i) →+* ℂ) (v : HeightOneSpectrum (𝓞 D.host.E)) (hv : v ∈ placesOver D.host.E (D.ntw.l i)) (τ : EmbV bkP i v hv), ∃ τc : D.host.E →+* ℂ, ReadEmb bkP i ι v hv τ τc ∧ ∀ (v' : HeightOneSpectrum (𝓞 D.host.E)) (hv' : v' ∈ placesOver D.host.E (D.ntw.l i)) (τ' : EmbV bkP i v' hv'), IsConjEmb bkP i v v' hv hv' τ τ' → ReadEmb bkP i ι v' hv' τ' (τc.comp (cj D)) := by
  intro D bkP i ι v hv τ
  obtain ⟨φ, hφ⟩ := exists_read (bkP.br i v hv) ι
  let c : D.host.E →+* ↥(bkP.br i v hv).Kw.1 :=
    ((bkP.br i v hv).j.comp (algebraMap D.host.E D.nd.Om)).codRestrict (bkP.br i v hv).Kw.1 (bkP.br i v hv).j_E
  have h : ReadEmb bkP i ι v hv τ ((φ.comp (AlgHom.toRingHom τ)).comp c) := by
    intro x n d hx
    have := congrArg φ hx.2
    rw [map_mul, hφ, hφ] at this
    exact this
  exact ⟨_, h, fun v' hv' τ' hc x n d hx => h _ n d ((hc x n d).1 hx)⟩

end GlobalTheory.ReadEmbEx

end
end
