module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CommuteRtOfMemZalg
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle484
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.Bundle004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1124
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PStringStepB
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsNormalisedOfIsDiscrete

@[expose] public section

section

noncomputable section

open NumberField MeasureTheory Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Affgl

namespace PositivityTheory.Rg.Rs.SliceTensor

theorem interp {K : Type} (A : Submodule ℂ (K → ℂ)) [FiniteDimensional ℂ A] :
    ∃ (S : Finset K) (a : S → A), ∀ c ∈ A, c = ∑ κ : S, c κ.1 • (a κ : K → ℂ) := by
  classical
  obtain ⟨S, hS⟩ := GlobalTheory.CompanionTheory.CTFin.UniSol.exists_finset_separating A
  let ev : A →ₗ[ℂ] (S → ℂ) := LinearMap.pi fun κ => (LinearMap.proj κ.1 : (K → ℂ) →ₗ[ℂ] ℂ) ∘ₗ A.subtype
  have hinj : LinearMap.ker ev = ⊥ := by
    refine LinearMap.ker_eq_bot'.2 fun c hc => Subtype.ext (hS c.1 c.2 fun κ hκ => ?_)
    exact congrFun hc ⟨κ, hκ⟩
  obtain ⟨P, hP⟩ := ev.exists_leftInverse_of_injective hinj
  refine ⟨S, fun κ => P (Pi.single κ 1), fun c hc => ?_⟩
  have h1 : P (ev ⟨c, hc⟩) = ⟨c, hc⟩ := LinearMap.congr_fun hP _
  have h2 : ev ⟨c, hc⟩ = ∑ κ : S, c κ.1 • (Pi.single κ 1 : S → ℂ) := by
    funext κ'
    simp [Finset.sum_apply, Pi.single_apply, ev]
  have h3 := congrArg Subtype.val h1

  rw [h2, map_sum] at h3
  simp only [map_smul, Submodule.coe_sum, Submodule.coe_smul] at h3
  exact h3.symm

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E]

theorem slice_mem {r s : ℕ} {L : Subgroup (GL (Fin (r + s)) (Af E))} {W : Type} [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ (Kinf E (r + s)) W) {J : Set (Module.End ℂ (Sm E (r + s)))} (hJ : J ⊆ Zalg E (r + s))
    {J₁ : Set (Module.End ℂ (Sm E r))}
    (H3 : ∀ F : Sm E (r + s), (∀ (x : BlockIx (r + s) r → Ad E) (g : GA E (r + s)), F.1 (unip x * g) = F.1 g) →
      (∀ z ∈ J, z F = 0) → ∀ G : Sm E r, (∀ m, G.1 m = F.1 (lev (Ad E) r s (m, 1))) → ∀ z ∈ J₁, z G = 0)
    (F : Sm E (r + s)) (hN : ∀ (x : BlockIx (r + s) r → Ad E) (g : GA E (r + s)), F.1 (unip x * g) = F.1 g)
    (hLv : ∀ k ∈ L, finRep E (r + s) k F = F)
    (hC : ∀ g : GA E (r + s), (fun k : Kinf E (r + s) => (cptRep E (r + s) k F).1 g) ∈ GlobalTheory.Published.AutFin.coeffSpan ρ)
    (hZ : ∀ z ∈ J, z F = 0) (t : GL (Fin (r + s)) (Af E)) (κ : Kinf E (r + s)) (m₂ : GA E s) (G : Sm E r)
    (hA : IsAutForm G)
    (hGv : ∀ m₁, G.1 m₁ = F.1 (lev (Ad E) r s (m₁, m₂) * finGL E (r + s) t * infGL E (r + s) (Unitary.toUnits κ))) :
    G ∈ genSpace (Slice1.levelOne s L t) (ρ.comp (Slice1.levK E r s)) J₁ := by
  let h : GA E (r + s) := lev (Ad E) r s (1, m₂) * finGL E (r + s) t * infGL E (r + s) (Unitary.toUnits κ)
  let F' := rt E (r + s) h F
  have hcoef : ∀ g : GA E r, (fun k : Kinf E r => (cptRep E r k G).1 g) ∈
      GlobalTheory.Published.AutFin.coeffSpan (ρ.comp (Slice1.levK E r s)) := by
    intro g
    have key := Slice1.coeff_comp ρ (Slice1.levK E r s) κ (hC (lev (Ad E) r s (g, m₂) * finGL E (r + s) t))
    convert key using 1
    funext k
    change G.1 (g * infGL E r (Unitary.toUnits k)) = F.1 (lev (Ad E) r s (g, m₂) * finGL E (r + s) t *
      infGL E (r + s) (Unitary.toUnits (Slice1.levK E r s k * κ)))
    rw [hGv, Slice1.lev_infGL_right, ← Slice1.toUnits_levK (s := s),
      ← map_mul (Unitary.toUnits : _ →* (Matrix (Fin (r + s)) (Fin (r + s)) (Cinf E))ˣ)]
  have hle : (Slice1.levelOne s L t : Set (GL (Fin r) (Af E))) ⊆ {k | finRep E r k G = G} := by
    intro k hk
    refine Subtype.ext (funext fun m => ?_)
    change G.1 (m * finGL E r k) = G.1 m
    rw [hGv, hGv]
    have hk' : F.1 (lev (Ad E) r s (m, m₂) * finGL E (r + s) t * infGL E (r + s) (Unitary.toUnits κ) *
        finGL E (r + s) (t⁻¹ * lev (Af E) r s (k, 1) * t)) =
        F.1 (lev (Ad E) r s (m, m₂) * finGL E (r + s) t * infGL E (r + s) (Unitary.toUnits κ)) :=
      congrFun (congrArg Subtype.val (hLv _ (Slice1.mem_levelOne.1 hk))) _
    rw [← hk', Slice1.lev_finGL_right]
  have hkill : ∀ z ∈ J₁, z G = 0 := by
    refine H3 F' (fun x g => ?_) (fun z hz => ?_) G (fun m => ?_)
    · change F.1 (unip x * g * h) = F.1 (g * h)
      rw [mul_assoc, hN]
    · change z (rt E (r + s) h F) = 0
      rw [← Module.End.mul_apply, (Slice1.commute_rt_of_mem_Zalg (hJ hz) h).eq, Module.End.mul_apply, hZ z hz, map_zero]
    · rw [hGv]
      change _ = F.1 (lev (Ad E) r s (m, 1) * h)
      have e : (m, m₂) = ((m, 1) * (1, m₂) : GA E r × GA E s) := by simp
      rw [e, map_mul]
      simp only [h, mul_assoc]
  exact ⟨hA, fun k hk => hle hk, hcoef, hkill⟩

end PositivityTheory.Rg.Rs.SliceTensor

end
end

section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin

namespace PositivityTheory.Rg.Rs

namespace PAscAll

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E]

theorem regInt_of_le {n : ℕ} {V : Submodule ℂ (Sm E n)} {τ : E →+* ℂ} {m m₁ : Multiset ℂ} {z : ℂ}
    (hnd : m.Nodup) (hint : ∀ x ∈ m, ∀ y ∈ m, ∃ k : ℤ, x - y = k) (hle : m₁.map (· + z) ≤ m)
    (h : HasInfCharGL V τ m₁) : RegInt V τ := by
  refine ⟨m₁, h, (Multiset.nodup_of_le hle hnd).of_map _, fun x hx y hy => ?_⟩
  obtain ⟨k, hk⟩ := hint (x + z) (Multiset.mem_of_le hle (Multiset.mem_map_of_mem _ hx))
    (y + z) (Multiset.mem_of_le hle (Multiset.mem_map_of_mem _ hy))
  exact ⟨k, by rw [← hk]; ring⟩

theorem exists_extremal (hF : ExpFin) (hN : ExpNeg) {N : ℕ} (V : Submodule ℂ (Sm E N)) (hV : IsDiscrete V)
    (hne : ∃ r, 0 < r ∧ r < N ∧ (ExpV r V).Nonempty) :
    ∃ (r : ℕ) (c : ℂ) (lam : ℝ), 0 < r ∧ r < N ∧ c ∈ ExpV r V ∧ 0 < lam ∧
      pE E N r c = -lam * (r * ((N : ℝ) - r)) ∧
      ∀ m, 0 < m → m < N → ∀ c' ∈ ExpV m V, pE E N m c' ≤ -lam * (m * ((N : ℝ) - m)) := by
  set S : Set (ℕ × ℂ) := {p | 0 < p.1 ∧ p.1 < N ∧ p.2 ∈ ExpV p.1 V} with hSdef
  have hfin : S.Finite := by
    refine ((Set.finite_Ioo 0 N).biUnion fun r hr => (hF E N V hV r hr.1 hr.2).image (Prod.mk r)).subset ?_
    intro p hp
    exact Set.mem_iUnion₂.2 ⟨p.1, ⟨hp.1, hp.2.1⟩, p.2, hp.2.2, rfl⟩
  obtain ⟨r₀, hr₀, hr₀N, c₀, hc₀⟩ := hne
  have hD : ∀ m : ℕ, 0 < m → m < N → (0 : ℝ) < m * ((N : ℝ) - m) := fun m h0 h1 =>
    mul_pos (by exact_mod_cast h0) (sub_pos.2 (by exact_mod_cast h1))
  let f : ℕ × ℂ → ℝ := fun p => -pE E N p.1 p.2 / ((p.1 : ℝ) * ((N : ℝ) - p.1))
  obtain ⟨⟨r, c⟩, ⟨hr, hrN, hc⟩, hmin⟩ := Set.exists_min_image S f hfin ⟨(r₀, c₀), hr₀, hr₀N, hc₀⟩
  have hneg : pE E N r c < 0 := by
    obtain ⟨φ, hφ, hcφ⟩ := hc
    exact hN E N φ (hV.aut φ hφ) (hV.sqInt φ hφ) r hr hrN c hcφ
  refine ⟨r, c, f (r, c), hr, hrN, hc, div_pos (neg_pos.2 hneg) (hD r hr hrN), ?_, ?_⟩
  · simp only [f]
    rw [neg_mul, div_mul_cancel₀ _ (hD r hr hrN).ne', neg_neg]
  · intro m hm hmN c' hc'
    have h1 := (le_div_iff₀ (hD m hm hmN)).1 (hmin (m, c') ⟨hm, hmN, hc'⟩)
    linarith [neg_mul (f (r, c)) ((m : ℝ) * ((N : ℝ) - m))]

end PAscAll

theorem ascAll_of (hD : Dich) (hF : ExpFin) (hN : ExpNeg) (hS : Slice) (hC : Chord) (hP : Proj) (hI : InfInd2)
    (hSS : StringStep) (hSt : Stages) : AscAll := by
  intro E _ _ _ N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro hN1 V hV τ hτ
  rcases hD E N hN1 V hV with ⟨π, hu, hn, h⟩ | hne
  · exact ⟨N, 1, π, hu, hn, h⟩
  obtain ⟨r, c, lam, hr0, hrN, hc, hlam, hpc, hbd⟩ := PAscAll.exists_extremal hF hN V hV hne
  obtain ⟨s, rfl⟩ : ∃ s, N = r + s := ⟨N - r, by omega⟩
  have hs0 : 0 < s := by omega
  have hd : (0 : ℝ) < (Module.finrank ℚ E : ℝ) := by exact_mod_cast Module.finrank_pos
  have hdC : (Module.finrank ℚ E : ℂ) ≠ 0 := by exact_mod_cast Module.finrank_pos.ne'
  have hpc' : pE E (r + s) r c = -lam * (r * s) := by rw [hpc]; push_cast; ring
  obtain ⟨T, hT⟩ := hS E r s hr0 hs0 V hV c hc
  have hL2 := hC E r s hr0 hs0 V c T lam hlam hT hpc' hbd
  obtain ⟨V₁, V₂, hV₁, hV₂, hemb⟩ := hP E r s hr0 hs0 V hV c _ _ T hT hL2
  obtain ⟨m, hm, hnd, hint⟩ := hτ
  obtain ⟨m₁, m₂, hm₁, hm₂, he⟩ := hI E r s V V₁ V₂ _ _ hV hV₁ hV₂ hemb τ m hm
  have hτ₁ : RegInt V₁ τ := PAscAll.regInt_of_le hnd hint (he ▸ Multiset.le_add_right _ _) hm₁
  have hτ₂ : RegInt V₂ τ := PAscAll.regInt_of_le hnd hint (he ▸ Multiset.le_add_left _ _) hm₂
  obtain ⟨a₁, d₁, π₁, hu₁, hn₁, h₁⟩ := ih r (by omega) hr0 V₁ hV₁ τ hτ₁
  obtain ⟨a₂, d₂, π₂, hu₂, hn₂, h₂⟩ := ih s (by omega) hs0 V₂ hV₂ τ hτ₂
  have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast hr0.ne'
  have hs' : (s : ℂ) ≠ 0 := by exact_mod_cast hs0.ne'
  have hsum : (r : ℂ) * (c / (r * (Module.finrank ℚ E : ℂ))) + s * (-c / (s * (Module.finrank ℚ E : ℂ))) = 0 := by
    field_simp; ring
  have hre : (c / (r * (Module.finrank ℚ E : ℂ))).re < (s : ℝ) / 2 := by
    have e : (r : ℂ) * (Module.finrank ℚ E : ℂ) = (((r : ℝ) * (Module.finrank ℚ E : ℝ) : ℝ) : ℂ) := by push_cast; ring
    have hrR : (0 : ℝ) < r := by exact_mod_cast hr0
    rw [e, Complex.div_ofReal_re, div_lt_iff₀ (mul_pos hrR hd)]
    have h3 : c.re / (Module.finrank ℚ E : ℝ) < (r : ℝ) * s / 2 := by
      have h4 := hpc'
      unfold pE at h4
      push_cast at h4
      nlinarith [mul_pos hlam (mul_pos hrR (show (0 : ℝ) < s by exact_mod_cast hs0))]
    rw [div_lt_iff₀ hd] at h3
    nlinarith
  obtain ⟨hsig, hz₁, hz₂⟩ := hSS E r s hr0 hs0 V V₁ V₂ _ _ hV hV₁ hV₂ hemb τ ⟨m, hm, hnd, hint⟩ hsum hre
    a₁ d₁ a₂ d₂ π₁ π₂ hu₁ hn₁ (h₁ π₁ (Setoid.refl π₁)) hu₂ hn₂ (h₂ π₂ (Setoid.refl π₂))
  obtain ⟨rfl, hq⟩ := Sigma.mk.inj_iff.mp hsig
  have hiso : π₁.Iso π₂ := Quotient.exact (eq_of_heq hq)
  rw [hz₁, hz₂] at hemb
  refine ⟨a₁, d₁ + d₂, π₁, hu₁, hn₁, fun π' h' => ?_⟩
  exact hSt E r s a₁ d₁ d₂ V V₁ V₂ π' hV hV₁ hV₂ hemb (h₁ π' h') (h₂ π' ((CuspSub.setoid E a₁).iseqv.trans ((CuspSub.setoid E a₁).iseqv.symm hiso) h'))

end PositivityTheory.Rg.Rs

end
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.Rs

def LocSub : Prop := ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (N a d : ℕ) (V : Submodule ℂ (Sm E N)) (π : CuspSub E a), 1 ≤ N → IsDiscrete V →
  AscEmb V π d → ∀ (w : HeightOneSpectrum (𝓞 E)) (σ : SmIrr (GL (Fin a) (w.adicCompletion E)))
    (σ' : SmIrr (GL (Fin N) (w.adicCompletion E))), π.IsLocComp w σ → IsLocCompGL V w σ' →
    ∃ hd : ∑ i : Fin d, (GlobalTheory.LocGL.spehFactor (GlobalTheory.LocGL.IrrGL.of σ.ρ σ.smooth σ.irred) d i.rev).1 = N,
      ∃ f : σ'.ρ.IntertwiningMap (GlobalTheory.LocGL.prodIrr
        (fun i : Fin d => GlobalTheory.LocGL.spehFactor (GlobalTheory.LocGL.IrrGL.of σ.ρ σ.smooth σ.irred) d i.rev) hd), f ≠ 0

def LocDual : Prop := ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [CharZero k] (N d : ℕ) (x : GlobalTheory.LocGL.IrrGL (k := k)) (σ' : SmIrr (GL (Fin N) k)), IsUnitarisable x.rep → IsUnitarisable σ'.ρ →
  ∀ (hd : ∑ i : Fin d, (GlobalTheory.LocGL.spehFactor x d i.rev).1 = N)
    (f : σ'.ρ.IntertwiningMap (GlobalTheory.LocGL.prodIrr (fun i : Fin d => GlobalTheory.LocGL.spehFactor x d i.rev) hd)), f ≠ 0 →
    ∃ hd' : ∑ i, (GlobalTheory.LocGL.spehFactor x d i).1 = N,
      ∃ g : (GlobalTheory.LocGL.prodIrr (GlobalTheory.LocGL.spehFactor x d) hd').IntertwiningMap σ'.ρ, Function.Surjective g

def Clause3Asc : Prop := ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (N a d : ℕ) (V : Submodule ℂ (Sm E N)) (π : CuspSub E a), 1 ≤ N → IsDiscrete V →
  π.IsUnitary → IsNormalised π → AscEmb V π d → ∀ w σ σ', π.IsLocComp w σ → IsLocCompGL V w σ' →
    GlobalTheory.LocGL.IsSpeh (GlobalTheory.LocGL.IrrGL.of σ.ρ σ.smooth σ.irred) d σ'.ρ

def AscSeed : Prop := AscAll ∧ Clause3Asc

end PositivityTheory.Rg.Rs

end
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.UG
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.LFun GlobalTheory.PRep

namespace PositivityTheory.Rg.Rs.SatakeVectors

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E]

theorem finRep_mulChi {m : ℕ} (χ : HChar E) (w : HeightOneSpectrum (𝓞 E)) (g : GL (Fin m) (w.adicCompletion E))
    (x : Sm E m) :
    finRep E m (locGL E m w g) (mulChi m χ x) =
      ((χ.loc w (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) • mulChi m χ (finRep E m (locGL E m w g) x) := by
  have := act_mulChi (o := (Op.fin (locGL E m w g) : Op E m)) χ x
  rw [opAdd, zero_smul, add_zero, opMul, CuspSub.chiDet_locGL, map_smul] at this
  exact this

theorem satLike_map_mulChi {m : ℕ} {V : Submodule ℂ (Sm E m)} {w : HeightOneSpectrum (𝓞 E)} {B : Multiset ℂˣ}
    {χ : HChar E} (hχ : χ.UnrAt w) (h : SatLike V w B) :
    SatLike (V.map (mulChi m χ).toLinearMap) w (B.map (· * χ.val w)) := by
  intro ψ hψ hK h0
  obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.1 hψ
  have hxK : ∀ k ∈ KGL w (n := m), finRep E m (locGL E m w k) x = x := fun k hk => by
    have e := hK k hk
    rw [LinearEquiv.coe_coe, finRep_mulChi, hχ _ (GlobalTheory.SphGal.isUnitAt_det_of_mem hk), Units.val_one,
      one_smul] at e
    exact (mulChi m χ).injective e
  have hx0 : x ≠ 0 := fun e => h0 (by rw [e, map_zero])
  have hs := h x hx hxK hx0
  refine ⟨h0, GlobalTheory.LGrp.mem_fixed.2 fun k hk => hK k hk, by rw [Multiset.card_map, hs.2.2.1],
    fun ϖ hϖ j hj => ?_⟩
  rw [LinearEquiv.coe_coe, GlobalTheory.SphGal.satEig_map_mul, mul_smul, ← map_smul (mulChi m χ),
    ← hs.2.2.2 ϖ hϖ j hj, heckeVec, heckeVec]
  have e := (mulChi m χ).toAddEquiv.map_finsum
    (fun c : _ ⧸ KGL w (n := m) => Tj ℂ m (Ov E w) ϖ j c.out • ((finRep E m).comp (locGL E m w)) c.out x)
  rw [show (mulChi m χ) _ = _ from e, smul_finsum]
  refine finsum_congr fun c => ?_
  by_cases hc : Tj ℂ m (Ov E w) ϖ j c.out = 0
  · simp [hc]
  · change Tj ℂ m (Ov E w) ϖ j c.out • finRep E m (locGL E m w c.out) (mulChi m χ x) = _
    rw [finRep_mulChi, GlobalTheory.SphGal.loc_det_of_Tj hχ hϖ hj hc, smul_comm]
    simp

open GlobalTheory.Mem.Chr.CharModel in
omit [_root_.NumberField.IsTotallyComplex E] in
theorem unrAt_absC (s : ℂ) (w : HeightOneSpectrum (𝓞 E)) : (Model.absC E s).UnrAt w := fun x hx => Units.ext (by
  change Complex.exp (s * logNorm E (GlobalTheory.Mem.Chr.localIdele E w x)) = 1
  rw [logNorm_local w x 0 (by simpa [Formalism.L2.Host.IsUnitAt] using hx)]; simp)

open GlobalTheory.Mem.Chr.CharModel in
theorem val_absC (s : ℂ) (w : HeightOneSpectrum (𝓞 E)) : (Model.absC E s).val w = qU w (-s) := Units.ext (by
  change Complex.exp (s * logNorm E (GlobalTheory.Mem.Chr.localIdele E w (Formalism.L2.Host.atFin w (Formalism.L2.Host.unif w)))) = _
  have h0 : (Ideal.absNorm w.asIdeal : ℕ) ≠ 0 := by simpa [Ideal.absNorm_eq_zero_iff] using w.ne_bot
  rw [qU_val, logNorm_local w _ 1 (Formalism.L2.Host.unif_spec w), Complex.cpow_def_of_ne_zero (by exact_mod_cast h0),
    ← Complex.natCast_log]
  congr 1; push_cast; ring)

theorem satLike_tw {m : ℕ} {V : Submodule ℂ (Sm E m)} {w : HeightOneSpectrum (𝓞 E)} {B : Multiset ℂˣ}
    (h : SatLike V w B) (z : ℂ) : SatLike (tw V z) w (B.map (· * qU w (-z))) := by
  have := satLike_map_mulChi (unrAt_absC z w) h
  rw [val_absC] at this
  exact this

end PositivityTheory.Rg.Rs.SatakeVectors

end
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec
open scoped ComplexConjugate

namespace PositivityTheory.Rg.Rs.StrStepC

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E]

def twL {a₁ a₂ d₁ d₂ : ℕ} (π₁ : CuspSub E a₁) (π₂ : CuspSub E a₂) (x : Fin d₁ → ℂ) (y : Fin d₂ → ℂ) :
    List (Σ a, CG E a) :=
  List.ofFn (fun i => (⟨a₁, (CG.mk π₁).twist (GlobalTheory.CuspRep.Model.absC E (x i))⟩ : Σ a, CG E a)) ++
    List.ofFn (fun j => (⟨a₂, (CG.mk π₂).twist (GlobalTheory.CuspRep.Model.absC E (y j))⟩ : Σ a, CG E a))

theorem map_fsum {α β ι : Type} (f : α → β) (s : Finset ι) (g : ι → Multiset α) :
    (∑ i ∈ s, g i).map f = ∑ i ∈ s, (g i).map f :=
  map_sum (Multiset.mapAddMonoidHom f) g s

omit [_root_.NumberField.IsTotallyComplex E] in
theorem absNorm_ne_zero (w : HeightOneSpectrum (𝓞 E)) : ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ≠ 0 := by
  have := NumberField.HeightOneSpectrum.one_lt_absNorm w
  exact_mod_cast (by omega : Ideal.absNorm w.asIdeal ≠ 0)

theorem hinv_absC (w : HeightOneSpectrum (𝓞 E)) (x : ℂ) :
    (star ((GlobalTheory.CuspRep.Model.absC E x).val w))⁻¹ = (GlobalTheory.CuspRep.Model.absC E (-conj x)).val w := by
  apply Units.ext
  rw [Units.val_inv_eq_inv_val, Units.coe_star, StrStepB.absC_val, StrStepB.absC_val]
  have hq : (((Ideal.absNorm w.asIdeal : ℕ) : ℂ)).arg ≠ Real.pi := by
    rw [Complex.natCast_arg]; exact Real.pi_ne_zero.symm
  have h1 := Complex.cpow_conj ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) (-x) hq
  rw [Complex.conj_natCast] at h1
  change (conj (((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (-x)))⁻¹ = _
  rw [← h1, ← Complex.cpow_neg, map_neg, neg_neg]


omit [_root_.NumberField.IsTotallyComplex E] in
theorem satTw_string (w : HeightOneSpectrum (𝓞 E)) (z : ℂ) (C B₀ : Multiset ℂˣ) {d : ℕ} (e : Fin d → ℝ)
    (h : C.map (fun b : ℂˣ => (b : ℂ)) = ∑ i, satTw w (e i : ℂ) B₀) :
    satTw w z C = ∑ i, B₀.map fun b : ℂˣ => (b : ℂ) * ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (-(z + (e i : ℂ))) := by
  have e1 : satTw w z C = (C.map fun b : ℂˣ => (b : ℂ)).map
      (fun c => c * ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (-z)) := by
    unfold satTw; congr 1
    exact Multiset.bind_singleton _ _
  rw [e1, h, map_fsum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have e2 : satTw w (e i : ℂ) B₀ = (B₀.map fun b : ℂˣ => (b : ℂ)).map
      (fun c => c * ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (-(e i : ℂ))) := by
    unfold satTw; congr 1
    exact Multiset.bind_singleton _ _
  rw [e2, Multiset.map_map, Multiset.map_map]
  refine Multiset.map_congr rfl fun b _ => ?_
  simp only [Function.comp_apply]
  rw [neg_add, Complex.cpow_add _ _ (absNorm_ne_zero w)]
  ring

theorem sat_expand (hI : SatInd2) (hA : SatAsc) (hH : SatHerm) {r s : ℕ} (V : Submodule ℂ (Sm E (r + s)))
    (V₁ : Submodule ℂ (Sm E r)) (V₂ : Submodule ℂ (Sm E s)) (z₁ z₂ : ℂ) (hV : IsDiscrete V) (hV₁ : IsDiscrete V₁)
    (hV₂ : IsDiscrete V₂) (hemb : Emb V (MemInd2 (tw V₁ z₁) (tw V₂ z₂))) {a₁ d₁ a₂ d₂ : ℕ} (π₁ : CuspSub E a₁)
    (π₂ : CuspSub E a₂) (ha₁ : 1 ≤ a₁) (ha₂ : 1 ≤ a₂) (hu₁ : π₁.IsUnitary) (hn₁ : IsNormalised π₁)
    (hu₂ : π₂.IsUnitary) (hn₂ : IsNormalised π₂) (h₁ : AscEmb V₁ π₁ d₁) (h₂ : AscEmb V₂ π₂ d₂) :
    ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ∃ BV B₁ B₂ : Multiset ℂˣ, SatV V w BV ∧
      (CG.mk π₁).HasSat w B₁ ∧ (CG.mk π₂).HasSat w B₂ ∧
      BV.map (fun b : ℂˣ => (b : ℂ)) =
        (∑ i : Fin d₁, B₁.map fun b : ℂˣ =>
          (b : ℂ) * ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (-(z₁ - (s : ℂ) / 2 + (spehExp d₁ i : ℂ)))) +
          ∑ j : Fin d₂, B₂.map (fun b : ℂˣ =>
            (b : ℂ) * ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (-(z₂ + (r : ℂ) / 2 + (spehExp d₂ j : ℂ)))) ∧
      BV.map (fun b => (star b)⁻¹) = BV ∧ B₁.map (fun b => (star b)⁻¹) = B₁ ∧ B₂.map (fun b => (star b)⁻¹) = B₂ := by
  filter_upwards [hI E r s V V₁ V₂ z₁ z₂ hV hV₁ hV₂ hemb, hA E r a₁ d₁ V₁ π₁ hV₁ h₁,
    hA E s a₂ d₂ V₂ π₂ hV₂ h₂] with w hw hw₁ hw₂
  obtain ⟨B, C₁, C₂, hB, hC₁, hC₂, e⟩ := hw
  obtain ⟨B₁, hs₁, hall₁⟩ := hw₁
  obtain ⟨B₂, hs₂, hall₂⟩ := hw₂
  refine ⟨B, B₁, B₂, hB, hs₁, hs₂, ?_, (hH E (r + s) w B).1 V hV hB, (hH E a₁ w B₁).2 π₁ ha₁ hu₁ hn₁ hs₁,
    (hH E a₂ w B₂).2 π₂ ha₂ hu₂ hn₂ hs₂⟩
  rw [e, satTw_string w _ C₁ B₁ (spehExp d₁) (hall₁ C₁ hC₁), satTw_string w _ C₂ B₂ (spehExp d₂) (hall₂ C₂ hC₂)]

theorem perm_of (hR : GlobalTheory.Published.JacquetShalikaRigidity) {a₁ a₂ d₁ d₂ : ℕ} (π₁ : CuspSub E a₁) (π₂ : CuspSub E a₂)
    (ha₁ : 1 ≤ a₁) (ha₂ : 1 ≤ a₂) (x : Fin d₁ → ℂ) (y : Fin d₂ → ℂ)
    (hw : ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ∃ BV B₁ B₂ : Multiset ℂˣ,
      (CG.mk π₁).HasSat w B₁ ∧ (CG.mk π₂).HasSat w B₂ ∧
      BV.map (fun b : ℂˣ => (b : ℂ)) =
        (∑ i, B₁.map fun b : ℂˣ => (b : ℂ) * ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (-x i)) +
          ∑ j, B₂.map (fun b : ℂˣ => (b : ℂ) * ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (-y j)) ∧
      BV.map (fun b => (star b)⁻¹) = BV ∧ B₁.map (fun b => (star b)⁻¹) = B₁ ∧ B₂.map (fun b => (star b)⁻¹) = B₂) :
    (twL π₁ π₂ x y).Perm (twL π₁ π₂ (fun i => -conj (x i)) (fun j => -conj (y j))) := by
  classical
  have hpos : ∀ (x' : Fin d₁ → ℂ) (y' : Fin d₂ → ℂ), ∀ p ∈ twL π₁ π₂ x' y', 1 ≤ p.1 := by
    intro x' y' p hp
    simp only [twL, List.mem_append, List.mem_ofFn] at hp
    rcases hp with ⟨i, rfl⟩ | ⟨j, rfl⟩
    · exact ha₁
    · exact ha₂
  refine hR.perm _ _ (hpos _ _) (hpos _ _) (hw.mono fun w hw' => ?_)
  obtain ⟨BV, B₁, B₂, h₁, h₂, e, hV, hh₁, hh₂⟩ := hw'
  let B : (Σ a, CG E a) → Multiset ℂˣ := fun p => if h : ∃ B, p.2.HasSat w B then h.choose else 0
  have hB : ∀ p (B' : Multiset ℂˣ), p.2.HasSat w B' → B p = B' := fun p B' h => by
    have hex : ∃ B, p.2.HasSat w B := ⟨B', h⟩
    simp only [B, dif_pos hex]
    exact hex.choose_spec.unique h
  have t₁ : ∀ u : ℂ, B ⟨a₁, (CG.mk π₁).twist (GlobalTheory.CuspRep.Model.absC E u)⟩ =
      B₁.map (· * (GlobalTheory.CuspRep.Model.absC E u).val w) :=
    fun u => hB _ _ (StrStepB.hasSat_twist_absC π₁ h₁ u)
  have t₂ : ∀ u : ℂ, B ⟨a₂, (CG.mk π₂).twist (GlobalTheory.CuspRep.Model.absC E u)⟩ =
      B₂.map (· * (GlobalTheory.CuspRep.Model.absC E u).val w) :=
    fun u => hB _ _ (StrStepB.hasSat_twist_absC π₂ h₂ u)
  have hsat : ∀ (x' : Fin d₁ → ℂ) (y' : Fin d₂ → ℂ), ∀ p ∈ twL π₁ π₂ x' y', p.2.HasSat w (B p) := by
    intro x' y' p hp
    simp only [twL, List.mem_append, List.mem_ofFn] at hp
    rcases hp with ⟨i, rfl⟩ | ⟨j, rfl⟩
    · rw [t₁]; exact StrStepB.hasSat_twist_absC π₁ h₁ _
    · rw [t₂]; exact StrStepB.hasSat_twist_absC π₂ h₂ _
  refine ⟨B, hsat x y, hsat _ _, ?_⟩
  simp only [twL, List.map_append, List.map_ofFn, List.sum_append, List.sum_ofFn, Function.comp_def, t₁, t₂]
  have hT : (∑ i, B₁.map (· * (GlobalTheory.CuspRep.Model.absC E (x i)).val w)) +
      ∑ j, B₂.map (· * (GlobalTheory.CuspRep.Model.absC E (y j)).val w) = BV := by
    apply Multiset.map_injective (f := fun b : ℂˣ => (b : ℂ)) Units.val_injective
    rw [e, Multiset.map_add (f := _), map_fsum, map_fsum]
    congr 1 <;> refine Finset.sum_congr rfl fun i _ => ?_ <;> rw [Multiset.map_map] <;>
      refine Multiset.map_congr rfl fun b _ => ?_ <;> simp [StrStepB.absC_val]
  have hm : ∀ (C : Multiset ℂˣ) (u : ℂˣ), C.map (fun b => (star b)⁻¹) = C →
      (C.map (· * u)).map (fun b => (star b)⁻¹) = C.map (· * (star u)⁻¹) := by
    intro C u hC
    conv_rhs => rw [← hC]
    rw [Multiset.map_map, Multiset.map_map]
    refine Multiset.map_congr rfl fun b _ => ?_
    simp [star_mul', mul_comm]
  calc _ = BV := hT
    _ = BV.map (fun b => (star b)⁻¹) := hV.symm
    _ = _ := by
      rw [← hT, Multiset.map_add (f := _), map_fsum, map_fsum]
      simp only [hm B₁ _ hh₁, hm B₂ _ hh₂, hinv_absC]

end PositivityTheory.Rg.Rs.StrStepC

end
end
