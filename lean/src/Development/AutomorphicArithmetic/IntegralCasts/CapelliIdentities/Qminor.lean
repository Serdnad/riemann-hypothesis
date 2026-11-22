import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.QuantumMinorsCasimir

noncomputable section

namespace UpperTheory.Reformulated.B.Qf10

def GlRel {A : Type*} [Ring A] {n : ℕ} (E : Fin n → Fin n → A) : Prop :=
  UpperTheory.Reformulated.B.QuantumMinorsCasimir.GlRel E

def Tm {A : Type*} [inst : Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A) (u : ℂ) (a b : Fin n) : A :=
  UpperTheory.Reformulated.B.QuantumMinorsCasimir.Tm E u a b

def qminor {A : Type*} [inst : Ring A] [Algebra ℂ A] {n t : ℕ} (E : Fin n → Fin n → A)
    (a b : Fin t → Fin n) (u : ℂ) : A :=
  UpperTheory.Reformulated.B.QuantumMinorsCasimir.qminor E a b u

def qdet {A : Type*} [inst : Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A) (u : ℂ) : A :=
  UpperTheory.Reformulated.B.QuantumMinorsCasimir.qdet E u

theorem casimir {V : Type} [inst : AddCommGroup V] [inst_1 : Module ℂ V] (E : Fin 2 → Fin 2 → Module.End ℂ V)
    (h : GlRel E) (k : ℂ) (φ : V)
    (h1 : E 0 0 φ + E 1 1 φ = 0)
    (h2 : E 0 1 φ - E 1 0 φ = (Complex.I * k) • φ)
    (h3 : E 0 0 φ - E 1 1 φ = Complex.I • (E 0 1 φ + E 1 0 φ)) (u : ℂ) :
    qdet E (u + 1 / 2) φ = ((u + (k - 1) / 2) * (u - (k - 1) / 2)) • φ :=
  UpperTheory.Reformulated.B.QuantumMinorsCasimir.casimir E h k φ h1 h2 h3 u

end UpperTheory.Reformulated.B.Qf10
