module uberUFCG

abstract sig Valor {}
one sig DEBITO, CREDITO extends Valor {}

abstract sig Pessoa {
    valor: lone Valor
}
sig Motorista in Pessoa {}
sig Passageiro in Pessoa {}

abstract sig HoraIda {}
abstract sig HoraVolta {}
one sig SETEMEIA, NOVEMEIA, UMAMEIA, TRESMEIA extends HoraIda {}
one sig DEZ, DOZE, QUATRO, SEIS extends HoraVolta {}

abstract sig Regiao {}
one sig CENTRO, NORTE, SUL, LESTE, OESTE extends Regiao {}

abstract sig Corrida {
    motorista: one Motorista,
	passageiros: some Passageiro
}

sig Ida extends Corrida {
	regiaoOrigem: one Regiao,
    hora: one HoraIda
}

sig Volta extends Corrida {
	regiaoDestino: one Regiao,
    hora: one HoraVolta
}

fact RegrasCorrida {
    -- Uma corrida possui no máximo 3 passageiros além do motorista.
	all c: Corrida | #c.passageiros <= 3 and #c.passageiros >= 1
    
    -- Um motorista não pode ser também passageiro de uma mesma corrida.
    all c: Corrida | #(c.motorista & c.passageiros) = 0

    -- Uma pessoa não pode estar em duas corridas no mesmo horário.
    all disj i1, i2 : Volta |  (i1.hora = i2.hora) implies #(pessoasCorrida[i1] &  pessoasCorrida[i2]) = 0
	all disj v1, v2 : Ida |  (v1.hora = v2.hora) implies #(pessoasCorrida[v1] &  pessoasCorrida[v2]) = 0

    pessoaPodeSerAlunoProfessorServidor[]

    -- Calcula se uma determinada pessoa tem que pagar ou receber.
    all p: Pessoa | calculaValor[p]
}

fun pessoasCorrida[c: Corrida]: set Pessoa {
	c.motorista + c.passageiros
}

sig Aluno, Servidor, Professor in Passageiro + Motorista {}

pred pessoaPodeSerAlunoProfessorServidor[] {
    Pessoa = Aluno + Servidor + Professor

    no Professor & Aluno
    no Professor & Servidor
    no Servidor & Aluno
}

pred calculaValor[p: Pessoa] {
	(#p.~passageiros > #p.~motorista) implies p.valor = DEBITO
	(#p.~passageiros < #p.~motorista) implies p.valor = CREDITO
	(#p.~passageiros = #p.~motorista) implies no p.valor
}

--

pred show []{}
run show for 5
