module

public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
public import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

@[expose] public section

section

noncomputable section

namespace Formalism.MainNotions.SphericalInertData

open Formalism.BasicNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.ConjugateSelfDual Polynomial Filter

section Iso

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)

def IsBC (U : NBC A) (j : ℕ) (π : U.AU j) (Pa : List (Part A.CG)) : Prop :=
  (∀ p ∈ Pa, 1 ≤ p.a ∧ 1 ≤ p.d ∧ A.csd p.π) ∧
  (Pa.map fun p => ((⟨p.a, p.π⟩ : Σ a, A.CG a), p.d)).Nodup ∧
  rankIso N A Pa = R.nV ∧
  (∀ w, IsSplitPl H w → isoLoc N A Pa w = U.locAU j π w) ∧
  (∀ w, ¬ IsSplitPl H w → A.unr (isoLoc N A Pa w) ∧
    A.frobEig (isoLoc N A Pa w) = ubc R.nV (U.satAU j π w)) ∧
  ∀ τ, isoInf N A Pa τ = U.infW j (U.wtAU j π) τ

def SphInert (U : NBC A) (j : ℕ) (π : U.AU j) : Prop := ∀ w, ¬ IsSplitPl H w → U.sphAU j π w

end Iso

def HypCM (D : D7) : Prop :=
  (letI := D.host.cmStar; Formalism.HermitianLatticesTheory.IsCMUnram D.host.E) ∧
  2 ≤ Module.finrank ℚ D.host.F ∧
  ∀ w : PlE D.host, ¬ IsSplitPl D.host w → ((2 : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal

variable (D : D7)

def HypEFK : Prop :=
  Subfield.closure ((D.host.F : Set D.host.E) ∪ (D.host.K : Set D.host.E)) = ⊤

def BaseChangeSphericalInert : Prop :=
  HypCM D → ∀ j, 1 ≤ j → j ≤ D.R.m → 1 ≤ D.R.nV →
  (letI := D.host.cmStar; (D.sp.V j).IsDefinite) →
  ∀ π : D.nbc.AU j, SphInert D.nd D.naut D.nbc j π → ∃ Pa, IsBC D.nd D.naut D.nbc j π Pa

def Conclusion1 : Prop := HypEFK D → BaseChangeSphericalInert D

variable {D}

theorem isoLoc_single {a : ℕ} (P : D.naut.CG a) (w : PlE D.host) :
    isoLoc D.nd D.naut [⟨a, P, 1⟩] w = D.naut.locG P w := by
  have h0 : (((1 : ℕ) : ℝ) - 1) / 2 - ((0 : ℕ) : ℝ) = 0 := by norm_num
  show D.naut.lpSum (D.naut.lpSum (D.naut.lpTw (D.naut.locG P w) ((((1 : ℕ) : ℝ) - 1) / 2 - ((0 : ℕ) : ℝ)))
    (D.naut.lpZero w)) (D.naut.lpZero w) = D.naut.locG P w
  rw [D.naut.lpSum_zero, D.naut.lpSum_zero, h0, D.naut.lpTw_zero]


variable (D)

end Formalism.MainNotions.SphericalInertData

end
end

section

noncomputable section

namespace Formalism.MainNotions.N.Ln34

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

def FontExAll (D : D7) (HW : HWOf D.loc) (_F : FonOf D.loc D.locA HW) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (hG : Good K s LL)
    (T₀ T₁ T₂ : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (ι : LatHom T₀.L T₁.L) (π : LatHom T₁.L T₂.L),
    IsSESLat (Qp := ℚ_[l]) ι π →
    Function.Injective (((HW l).W K s LL hG).map ι) ∧ Function.Surjective (((HW l).W K s LL hG).map π) ∧
      ∀ x, ((HW l).W K s LL hG).map π x = 0 ↔ ∃ y, ((HW l).W K s LL hG).map ι y = x

end Formalism.MainNotions.N.Ln34

end
end

section

noncomputable section

namespace Formalism.MainNotions.N

def LocsCoverTw (D : Formalism.BasicNotions.D7) : Prop := ∀ j' w', 1 ≤ j' → j' ≤ D.R.m → D.what₂.muAt w' ≠ D.what₂.mu0 →
  ∑ i ∈ D.nd.locs j' w', Module.finrank (D.nd.O i) (D.nd.Mt i) =
    Module.finrank D.what₂.LL (D.what₂.MtL (D.what₂.muTw w') j')

end Formalism.MainNotions.N

end
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions

namespace Formalism.MainNotions.N

def WildTriv : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ), l.Prime →
    ∀ (v : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω), IsPlaceOver A v → v ∉ placesOver E l →
    ∀ (M : Type) [Group M] (φ : G E Ω →* M), IsOpen (φ.ker : Set (G E Ω)) → (∀ g, ∃ n : ℕ, φ g ^ (l ^ n) = 1) →
    ∀ σ : G E Ω, (∀ y : Ω, y ≠ 0 → A.valuation (σ y / y - 1) < 1) → φ σ = 1

theorem qpow_of_tw (hW : WildTriv) (D : D7) (i : D.nd.Loc) :
    ∀ v ∈ D.nd.Q i, ∀ g ∈ Ine (F := D.host.E) (D.nd.plOm.1 v),
      ∃ n : ℕ, D.nd.chi i 1 g = D.nd.chi i 1 (D.nd.gam0 i v) ^ n := by
  classical
  intro v hv g hg
  have hS : v ∉ D.nd.S i := fun h => Finset.disjoint_left.1 (D.nd.SQ_disj i) h hv
  have hl : v ∉ placesOver D.host.E (D.nd.l i) := D.nd.SQ_l i v (Or.inr hv)
  have hgk : ∀ k, v ∉ placesOver D.host.E (D.host.g k) := by
    intro k hk
    apply hS
    rw [D.nd.S_def i v]
    refine ⟨?_, hl⟩
    fin_cases k
    · exact Or.inl hk
    · exact Or.inr (Or.inl hk)
  have hpd : v ∉ D.ntw.pD (D.ntw.twOf i) := by
    intro hp
    have h' : v ∈ ((D.ntw.pD (D.ntw.twOf i) : Finset _) : Set (HeightOneSpectrum (𝓞 D.host.E))) := hp
    rw [D.ntw.pD_eq, D.ntw.twOf_l] at h'
    exact hS ((D.nd.S_def i v).2 ⟨Or.inr (Or.inr h'), hl⟩)
  have hl' : v ∉ placesOver D.host.E (D.ntw.l (D.ntw.twOf i)) := by
    rw [D.ntw.twOf_l]
    exact hl
  have hchi : ∀ h ∈ Ine (F := D.host.E) (D.nd.plOm.1 v), D.nd.chi i 1 h = D.ntw.psiL i h := by
    intro h hh
    have h1 := D.ntw.twistCharacterFamily_unramified (D.ntw.twOf i) (D.nd.j i) (D.ntw.twSide i) v hl' hgk hpd (D.nd.plOm.1 v)
      (D.nd.plOm.2 v) h hh
    rw [D.ntw.chi_tw i, MonoidHom.mul_apply, MonoidHom.comp_apply, h1, map_one, one_mul]
  rw [hchi g hg, hchi _ (D.nd.locNd_chebotarevPlace_mem i v)]
  obtain ⟨m, hm⟩ := D.ntw.psiL_ord i (D.nd.gam0 i v)
  have hL : 1 ≤ D.nd.l i ^ m := Nat.one_le_pow _ _ (Fact.out : (D.nd.l i).Prime).pos
  let H : Subgroup (G D.host.E D.nd.Om) :=
    { carrier := {x | ∃ n : ℕ, D.ntw.psiL i x = D.ntw.psiL i (D.nd.gam0 i v) ^ n}
      mul_mem' := by
        rintro a b ⟨n, hn⟩ ⟨k, hk⟩
        exact ⟨n + k, by rw [map_mul, hn, hk, pow_add]⟩
      one_mem' := ⟨0, by rw [map_one, pow_zero]⟩
      inv_mem' := by
        rintro a ⟨n, hn⟩
        refine ⟨n * (D.nd.l i ^ m - 1), ?_⟩
        rw [map_inv, hn]
        symm
        apply eq_inv_of_mul_eq_one_left
        rw [← pow_add, show n * (D.nd.l i ^ m - 1) + n = D.nd.l i ^ m * n by
          rw [mul_comm n, ← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel hL], pow_mul, hm, one_pow] }
  have hker : (D.ntw.psiL i).ker ≤ H := fun x hx => ⟨0, by rw [pow_zero]; exact hx⟩
  have hopen : IsOpen (H : Set (G D.host.E D.nd.Om)) := Subgroup.isOpen_mono hker (D.ntw.psiL_open i)
  have hclosed : IsClosed (H : Set (G D.host.E D.nd.Om)) := H.isClosed_of_isOpen hopen
  have hgen : Subgroup.closure (insert (D.nd.gam0 i v) {σ : G D.host.E D.nd.Om | ∀ y : D.nd.Om, y ≠ 0 →
      (D.nd.plOm.1 v).valuation (σ y / y - 1) < 1}) ≤ H := by
    rw [Subgroup.closure_le, Set.insert_subset_iff]
    refine ⟨⟨1, (pow_one _).symm⟩, fun σ hσ => ⟨0, ?_⟩⟩
    rw [pow_zero]
    exact hW D.host.E D.nd.Om (D.nd.l i) Fact.out v (D.nd.plOm.1 v) (D.nd.plOm.2 v) hl (D.nd.O i)ˣ
      (D.ntw.psiL i) (D.ntw.psiL_open i) (D.ntw.psiL_ord i) σ hσ
  have hT := (D.nd.restN_tameGenerator_generates i v (Or.inr hv)).2 hg
  exact closure_minimal hgen hclosed hT

end Formalism.MainNotions.N

end
end

section

noncomputable section

namespace Formalism.MainNotions.ArithmeticCylinders

open Formalism.BasicNotions Formalism.MainNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial Filter Topology
open scoped ComplexOrder

variable (D : D7)

def PointsLemma : Prop :=
  Disjoint (Formalism.CyclotomicNorms.BB D.R.r (D.host.g 0)) (Formalism.CyclotomicNorms.BB D.R.r (D.host.g 1)) →
  ∀ σ : D.what₂.FT, D.nd.goodRow σ →
    (∀ (k : Fin 2) (v : D.nd.PlG k),
      Formalism.MainNotions.N.TameGen D.nd (D.nd.plOm.1 (D.naut.plGw k v)) (D.ntypes.tg k v)) →
    D.ntypes.cuspidal σ ∧ ∀ w : D.what₂.places.Pl,
      haveI : Fact (D.what₂.places.resChar w).Prime := ⟨D.what₂.places.resChar_prime w⟩
      Formalism.CyclotomicNorms.IrredOn (D.ntypes.rbar σ w) ⊤ ∧
      (∀ k : Fin 2, D.what₂.places.resChar w ∉ Formalism.CyclotomicNorms.BB D.R.r (D.host.g k) →
        ∀ (Hs : Subgroup (G D.host.E D.nd.Om)) [Hs.Normal], IsOpen (Hs : Set (G D.host.E D.nd.Om)) →
          Group.IsSolvable (G D.host.E D.nd.Om ⧸ Hs) →
          (∀ u ∈ placesOver D.host.E (D.host.g k), Ine (F := D.host.E) (D.nd.plOm.1 u) ≤ Hs) →
          Formalism.CyclotomicNorms.IrredOn (D.ntypes.rbar σ w) Hs) ∧
      (∀ k : Fin 2, D.what₂.places.resChar w ≠ D.host.g k →
        haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
        ∀ (v : D.nd.PlG k) (j : Fin D.R.m) (u : (ZMod (D.host.g k))ˣ),
          u = D.nd.chiT k v j ∨ u = (D.nd.chiT k v j)⁻¹ →
          ¬ (Matrix.charpoly ((D.ntypes.rbar σ w (D.ntypes.tg k v) : GL (Fin D.R.r) _) :
              Matrix (Fin D.R.r) (Fin D.R.r) _)).IsRoot
            (D.ntypes.iota k v w (Formalism.CyclotomicNorms.primeToPart (D.what₂.places.resChar w)
              (algebraMap (ZMod (D.host.g k)) (Formalism.CyclotomicNorms.Fbar (D.host.g k))
                ((u : ZMod (D.host.g k)))))))

def TheoremThreePrime : Prop :=
  Disjoint (Formalism.CyclotomicNorms.BB D.R.r (D.host.g 0)) (Formalism.CyclotomicNorms.BB D.R.r (D.host.g 1)) →
  ∀ (i : D.nd.Loc) (Sig : List (Formalism.BasicNotions.Part D.naut.CG)),
    (∃ x, Formalism.MainNotions.N.HasParamX D.nd D.naut i x Sig) →
    (∀ (k : Fin 2) (v : D.nd.PlG k),
      (D.naut.items₂ k (D.naut.plGw k v) (Formalism.MainNotions.N.isoLoc D.nd D.naut Sig (D.naut.plGw k v))).natDegree =
        D.naut.lpDim (Formalism.MainNotions.N.isoLoc D.nd D.naut Sig (D.naut.plGw k v))) →
    Formalism.MainNotions.N.goodSig D.nd D.naut Sig →
    Formalism.MainNotions.N.IsCuspIso D.nd D.naut Sig ∧
    ∀ ρ : G D.host.E D.nd.Om →* GL (Fin D.R.r) (D.nd.O i), Formalism.MainNotions.N.IsRepOfSig D.nd D.naut i Sig ρ →
      Formalism.CyclotomicNorms.IrredOn (Formalism.MainNotions.N.mapRep ((D.naut.kFbar i).comp (IsLocalRing.residue (D.nd.O i))) ρ) ⊤ ∧
      (∀ k : Fin 2, D.nd.l i ∉ Formalism.CyclotomicNorms.BB D.R.r (D.host.g k) →
        ∀ (Hs : Subgroup (G D.host.E D.nd.Om)) [Hs.Normal], IsOpen (Hs : Set (G D.host.E D.nd.Om)) →
          Group.IsSolvable (G D.host.E D.nd.Om ⧸ Hs) →
          (∀ u ∈ placesOver D.host.E (D.host.g k), Ine (F := D.host.E) (D.nd.plOm.1 u) ≤ Hs) →
          Formalism.CyclotomicNorms.IrredOn (Formalism.MainNotions.N.mapRep ((D.naut.kFbar i).comp (IsLocalRing.residue (D.nd.O i))) ρ) Hs) ∧
      (∀ k : Fin 2, D.nd.l i ≠ D.host.g k → ∀ w ∈ placesOver D.host.E (D.host.g k),
        Formalism.MainNotions.N.TameGen D.nd (D.nd.plOm.1 w) (D.nd.gam0 i w) →
        ¬ (((Formalism.MainNotions.N.mapRep ((D.naut.kFbar i).comp (IsLocalRing.residue (D.nd.O i))) ρ (D.nd.gam0 i w) :
              GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) _).charpoly).IsRoot
          (D.naut.kFbar i (IsLocalRing.residue (D.nd.O i) (Formalism.MainNotions.N.chi1 D.nd i (D.nd.gam0 i w)))))

def atPlace (k : Fin 2) (v : D.nd.PlG k) (a : MonoidAlgebra ℂ (GL (Fin D.R.r) (ZMod (D.host.g k)))) :
    MonoidAlgebra ℂ (G0g D.nd) := by
  classical
  exact MonoidAlgebra.ofCoeff (Finsupp.mapDomain
    (fun h => Pi.mulSingle (M := fun kv : (Σ k : Fin 2, D.nd.PlG k) => GL (Fin D.R.r) (ZMod (D.host.g kv.1)))
      ⟨k, v⟩ h)
    a.coeff)

def labAct (τ : ℂ ≃+* ℂ) (k : Fin 2) (f : (ZMod (D.host.g k))[X]) : (ZMod (D.host.g k))[X] :=
  haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  Classical.epsilon fun f' : (ZMod (D.host.g k))[X] => f'.Monic ∧
    Formalism.CyclotomicNorms.rootsBar f' = (Formalism.CyclotomicNorms.rootsBar f).map
      (fun x => Function.invFun (D.ntypes.teichC k) (τ (D.ntypes.teichC k x)))

def IsLabel (k : Fin 2) (f : (ZMod (D.host.g k))[X]) : Prop :=
  f.Monic ∧ f.natDegree = D.R.r ∧ f.coeff 0 ≠ 0

def dualLab (k : Fin 2) (f : (ZMod (D.host.g k))[X]) : (ZMod (D.host.g k))[X] :=
  Polynomial.C (f.coeff 0)⁻¹ * f.reverse

abbrev Tup (k : Fin 2) : Type := D.nd.PlG k → (ZMod (D.host.g k))[X]

abbrev Tup2 : Type := ∀ k : Fin 2, D.nd.PlG k → (ZMod (D.host.g k))[X]

def cyl (k : Fin 2) (S : Set (Tup D k)) : Set (Tup2 D) := {t | t k ∈ S}

def wtOf (k : Fin 2) (a : MonoidAlgebra ℂ (GL (Fin D.R.r) (ZMod (D.host.g k))))
    (f : (ZMod (D.host.g k))[X]) : ℝ :=
  ((a * D.ntypes.eSer k f).coeff 1).re / (a.coeff 1).re

structure AllRows (D : D7) : Type 1 where
  B : Formalism.MainNotions.S.RowsAut
  n_eq : B.I.n = D.R.r
  f_eq : B.I.f = D.R.f
  labAll : ∀ k, Fin D.what₂.Dall → D.nd.PlG k → (ZMod (D.host.g k))[X]
  labAll_label : ∀ k σ v, IsLabel D k (labAll k σ v)
  inc : Fin D.what₂.Drows → Fin D.what₂.Dall
  eVec : ∀ k, D.nd.PlG k → MonoidAlgebra ℂ (GL (Fin D.R.r) (ZMod (D.host.g k)))
  eVec_idem : ∀ k v, eVec k v * eVec k v = eVec k v
  eT : Set (Tup2 D) → B.I.Gf → ℂ
  ReT : Set (Tup2 D) → (B.I.L2 B.μf B.fund →L[ℂ] B.I.L2 B.μf B.fund)
  ReT_spec : ∀ S, B.I.IsRConvF B.μf B.fund B.R (eT S) (ReT S)
  eT_univ : eT Set.univ = B.e
  ReT_univ : ReT Set.univ = B.Re
  eT_one : ∀ (k : Fin 2) (S : Finset (Tup D k)),
    (eT (cyl D k (S : Set (Tup D k))) 1).re =
      (B.e 1).re * ∑ t ∈ S, ∏ v, wtOf D k (eVec k v) (t v)

variable {D}

def AllRows.dimT (A : AllRows D) (S : Set (Tup2 D)) : ℕ :=
  A.B.I.Dcount A.B.σs A.B.μf A.B.fund A.B.R (A.ReT S)

def LabelCountGoodInjective (A : AllRows D) : Prop :=
  (∀ S : Set (Tup2 D), A.dimT S = Nat.card {τ : Fin D.what₂.Dall // (fun k => A.labAll k τ) ∈ S}) ∧
    Function.Injective A.inc ∧ (∀ k σ, A.labAll k (A.inc σ) = D.nd.lab k (D.what₂.ft σ)) ∧
    ∀ τ : Fin D.what₂.Dall, D.ntypes.goodTuple (fun k => A.labAll k τ) ↔ τ ∈ Set.range A.inc

variable (D)

def TieAdmG : Prop := ∀ k, D.ntypes.admissible (D.host.g k)

abbrev VecAt : Type :=
  ∀ k : Fin 2, D.nd.PlG k → MonoidAlgebra ℂ (GL (Fin D.R.r) (ZMod (D.host.g k)))

def entN {A : Type} [Zero A] {N : ℕ} (M : Matrix (Fin N) (Fin N) A) (a b : ℕ) : A :=
  if h : a < N ∧ b < N then M ⟨a, h.1⟩ ⟨b, h.2⟩ else 0

def IsUniUp {A : Type} [Zero A] [One A] {N : ℕ} (M : Matrix (Fin N) (Fin N) A) : Prop :=
  ∀ a b : Fin N, (b < a → M a b = 0) ∧ (a = b → M a b = 1)

def eDat (g N : ℕ) [NeZero g] (P : Matrix (Fin N) (Fin N) (ZMod g) → Prop)
    (φ : Matrix (Fin N) (Fin N) (ZMod g) → ZMod g) (ψ₀ : AddChar (ZMod g) ℂ) :
    MonoidAlgebra ℂ (GL (Fin N) (ZMod g)) := by
  classical
  exact ((Finset.univ.filter fun u : GL (Fin N) (ZMod g) => P (u : Matrix (Fin N) (Fin N) (ZMod g))).card : ℂ)⁻¹ •
    ∑ u ∈ Finset.univ.filter (fun u : GL (Fin N) (ZMod g) => P (u : Matrix (Fin N) (Fin N) (ZMod g))),
      MonoidAlgebra.single u (ψ₀ (φ (u : Matrix (Fin N) (Fin N) (ZMod g))))⁻¹

def eU (g N : ℕ) [NeZero g] (ψ₀ : AddChar (ZMod g) ℂ) : MonoidAlgebra ℂ (GL (Fin N) (ZMod g)) :=
  eDat g N IsUniUp (fun M => ∑ i ∈ Finset.range (N - 1), entN M i (i + 1)) ψ₀

def phiJ {g : ℕ} (kk s : ℕ) {N : ℕ} (M : Matrix (Fin N) (Fin N) (ZMod g)) : ZMod g :=
  (∑ i ∈ Finset.range (s - 1), entN M i (i + 1)) +
    (if 1 ≤ s then entN M (s - 1) (s + kk) + entN M (s + kk) (s + kk + 1) else 0) +
    (∑ i ∈ Finset.range (s - 1), entN M (s + kk + 1 + i) (s + kk + 2 + i)) +
    ∑ a ∈ Finset.range (kk - 1), entN M (s + a) (s + a + 1)

def eJ (g N : ℕ) [NeZero g] (kk s : ℕ) (ψ₀ : AddChar (ZMod g) ℂ) : MonoidAlgebra ℂ (GL (Fin N) (ZMod g)) :=
  eDat g N (fun M => IsUniUp M ∧ ∀ a, s ≤ a → a < s + kk → entN M a (s + kk) = 0) (phiJ kk s) ψ₀

def eUk (k : Fin 2) (ψ₀ : AddChar (ZMod (D.host.g k)) ℂ) :
    MonoidAlgebra ℂ (GL (Fin D.R.r) (ZMod (D.host.g k))) :=
  haveI : NeZero (D.host.g k) := ⟨(D.host.g_prime k).ne_zero⟩
  eU (D.host.g k) D.R.r ψ₀

def eJk (k : Fin 2) (ψ₀ : AddChar (ZMod (D.host.g k)) ℂ) :
    MonoidAlgebra ℂ (GL (Fin D.R.r) (ZMod (D.host.g k))) :=
  haveI : NeZero (D.host.g k) := ⟨(D.host.g_prime k).ne_zero⟩
  eJ (D.host.g k) D.R.r D.R.k (D.R.m / 2 - 1) ψ₀

def admLq : Prop :=
  ∀ (k : Fin 2) (ψ₀ : AddChar (ZMod (D.host.g k)) ℂ), ψ₀ ≠ 1 →
    haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
    (∀ f, 0 ≤ wtOf D k (eUk D k ψ₀) f ∧ 0 ≤ wtOf D k (eJk D k ψ₀) f) ∧
    (∀ f, IsLabel D k f → Squarefree f →
      wtOf D k (eUk D k ψ₀) f =
        1 / ((UniqueFactorizationMonoid.normalizedFactors f).map
          (fun P => (D.host.g k : ℝ) ^ P.natDegree - 1)).prod) ∧
    (∀ f, IsLabel D k f → (1 - 1 / (D.host.g k : ℝ)) * wtOf D k (eUk D k ψ₀) f ≤ wtOf D k (eJk D k ψ₀) f) ∧
    (∀ f, IsLabel D k f → Squarefree f →
      wtOf D k (eJk D k ψ₀) f ≤
        (1 + 1 / (D.host.g k : ℝ)) ^ D.R.r * wtOf D k (eUk D k ψ₀) f)

def goodAt (k : Fin 2) (t : Tup D k) : Prop :=
  haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  Formalism.CyclotomicNorms.IsGood D.R.r (D.host.g k) t (D.nd.chiT k) ∧
    Formalism.CyclotomicNorms.IsGood D.R.r (D.host.g k) t (fun v j => (D.nd.chiT k v j)⁻¹)

def locShare (eV : VecAt D) (k : Fin 2) (S : Finset (Tup D k)) : ℝ :=
  ∑ t ∈ S, ∏ v, wtOf D k (eV k v) (t v)

variable {D}

variable (D)

end Formalism.MainNotions.ArithmeticCylinders
end
end
