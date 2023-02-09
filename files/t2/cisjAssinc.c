/* 
Sistemas Distribuídos 2022/3 * Simulação com SMPL
Autor: Diogo Bortolini
Data da última atualização: 08/02/2023 - versão: 4
Funcionalidade: Detector de falhas vCube Assíncrono ambiente de simulação SMPL
*/

//Definindo as bibliotecas
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "smpl.h"

//Os tamanho dos clusters é uma potência de 2
#define POW_2(num) (1<<(num))
#define VALID_J(j, s) ((POW_2(s-1)) >= j)

/* vamos definir os eventos e booleano*/
#define TEST 0
#define FAULT 1
#define RECOVERY 2
#define SUSPECT 3

#define TRUE 1
#define FALSE 0

//CRIANDO AS ESTRUTURAS
/* |-- node_set.h */
typedef struct node_set {
	int* nodes;
	ssize_t size;
	ssize_t offset;
} node_set;

//Estutura da tabela C(i,s)
typedef struct {
    int cluster;
    int *cis;
} st_cis;

//Estrutura do nó
typedef struct {
    int id;
    int *states;
} st_no;

//Váriaveis globais
st_no *no;
int *info_no;
static int n;
static int num_cluster;
static int printar = 0;

//Variável t2
static int n_aleatorio = -1;

//Estrutura dos eventos para apresentar latência e demais dados a cada evento
typedef struct {
    int tipo;
    int latencia;
    int rodada;
    int number_test;
    int node_event;
    int teste;
} st_event;

st_event *events;

//Criando as funções
static node_set* set_new(ssize_t size)
{
	node_set* new;

	new = (node_set*)malloc(sizeof(node_set));
	new->nodes = (int*)malloc(sizeof(int)*size);
	new->size = size;
	new->offset = 0;
	return new;
}

static void set_insert(node_set* nodes, int node)
{
	if (nodes == NULL) return;
	nodes->nodes[nodes->offset++] = node;
}

static void set_merge(node_set* dest, node_set* source)
{
	if (dest == NULL || source == NULL) return;
	memcpy(&(dest->nodes[dest->offset]), source->nodes, sizeof(int)*source->size);
	dest->offset += source->size;
}

static void set_free(node_set* nodes)
{
	free(nodes->nodes);
	free(nodes);
}

static void print_nodes(node_set *nodes) {
    for (int i = 0; i < nodes->size; i++)
       printf("%i ", nodes->nodes[i]);
    puts("");
}
/* node_set.h --| */

//Função do cluster C(i,s)
node_set*
cis(int i, int s)
{
	node_set* nodes, *other_nodes;
	int xor = i ^ POW_2(s-1);
	int j;

	/* starting node list */
	nodes = set_new(POW_2(s-1));

	/* inserting the first value (i XOR 2^^(s-1)) */
	set_insert(nodes, xor);

	/* recursion */
	for (j=1; j<=s-1; j++) {
		other_nodes = cis(xor, j);
		set_merge(nodes, other_nodes);
		set_free(other_nodes);
	}
	return nodes;
}

//Função cria um novo evento e seta suas propriedades
void novoEvento(st_event *events, int rodada, int c_teste, int node, int tipo) {
    events[node].tipo = tipo; //tipo da falha
    events[node].latencia = 0; // contador de latencia
    events[node].rodada = rodada; // rodada de testes
    events[node].number_test = 0; //numero de testes realizados
    events[node].node_event = 1; //declara evento para nó
    events[node].teste = c_teste; //número do teste onde ocorre o evento
}

//Função que limpa um evento quando todos os processos corretos percebem ele
void limpaEvento(st_event *events, int node) {
    events[node].tipo = -1;
    events[node].latencia = -1;
    events[node].rodada = -1;
    events[node].number_test =-1;
    events[node].node_event =-1;
}

//Imprime os atributos de um evento
void imprimirEvento(st_event *events, int c_teste, int node) {
    if (events[node].node_event == 1) {
        printf("Processo: %d\n", node);
        if (events[node].tipo == FAULT) {
                printf("Tipo do Evento: FAULT\n");
        } 
        else if(events[node].tipo ==  SUSPECT) {
                printf("Tipo do Evento: Falsa Suspeita\n");
        }
        else printf("Tipo do Evento: RECOVERY\n");
        printf("Latência: %d\n", events[node].latencia); //Latência até todos os processos detectarem o evento
        printf("Rodada do evento: %d\n", events[node].rodada);
        printf("Testes após evento: %d\n", c_teste - events[node].teste); //Testes necessário p/ todos processos detectarem o evento
    }
}

//Retorna 1 quando todos os processos perceberem o evento
int atualizaEvento(st_event  *events, int node) {
    //Se é  FAULT
    if (events[node].tipo == FAULT) {
        if (events[node].node_event == 1 ) {
            for (int j = 0; j < n; j++) {
                if (info_no[j] == 1 && ((no[j].states[node] % 2) != 1) && node !=j)
                return 0;
            }
        }
        return 1;
    }
    //Se é RECOVERY
    else if (events[node].tipo == RECOVERY) {
        if (events[node].node_event == 1 ) {
            for (int j = 0; j < n; j++) {
                if (info_no[j] == 1 && ((no[j].states[node] % 2) != 0) && node !=j)
                return 0;
            }
        }
        return 1;
    }
}

//Popula a struct tabela_cis
//--------------------------------------------------------------------
void criaCIS (st_cis tabela_cis[n][num_cluster]) {
    int i, j, k, num_nos;
    node_set* nodes;
    for (i = 0; i < n; i++) {
        for (j = 0; j < num_cluster; j++) {
            num_nos = pow(2,j);
            tabela_cis[i][j].cluster = j + 1;
            tabela_cis[i][j].cis = (int *) malloc(sizeof(int)*num_nos);
            nodes = cis(i, j + 1);
            for (k = 0; k < num_nos; k++)
                tabela_cis[i][j].cis[k] = nodes->nodes[k];
        }
    }
}

//Imprime o State de cada nó
void imprimirState() { //imprime o State[] de cada processo que o testado sabe
    int i,j, k;
    for (i = 0; i < n; i++) {
        printf ("Processo %d STATE[",i);
        for (j = 0; j < n; j++)
            printf (" %d", no[i].states[j]);
        printf (" ]\n");
    }
    printf ("\n");
}

//Limpa o vetor State de um nó, colocando -1 (unknown)
void limpaState(int id) { //função para limpar os estados dos processos
    int i;
    for (i = 0; i < n; i++) {
        no[id].states[i] = -1; //Insere -1 (Unknown) no State[]
    }
}

//Compara o vetor state de um no com outro e atualiza
int atualizaState(int id, int node_tested) {
    int i, update = 0;
    for (i = 0; i < n; i++) {
        if (no[id].states[i] < no[node_tested].states[i]) {
            no[id].states[i] = no[node_tested].states[i];
            if (update == 0) {
                printf(", Processo %d ATUALIZOU state de [ %d", id, i);
                printar = 1; //Imprimir os States de todos os processos
                update = 1;
            } else {
                printf(" %d", i);
            }
        }
    }
    if (update == 1) {
        printf(" ]\n");
        return 1;
    }
    return 0;
}

//Gera a matriz dos testes a serem realizados 
void matrizTeste (int n, st_cis tabela_cis[n][num_cluster], int test[n][n]) {
    int i, j, k;

    for (i = 0; i < n; i++ ) {
        for (j = 0; j < n; j++) {
            test[i][j] = 0;
        }
    }

    for (i = 0; i < n; i++) {
        for (j = 0; j < num_cluster; j++) {
            k = 0;
            while (info_no[tabela_cis[i][j].cis[k]] == 0 && k < pow(2,j)) {
                k++;
            }
            if (info_no[tabela_cis[i][j].cis[k]] == 1 && tabela_cis[i][j].cis[k] != i) {
                test[tabela_cis[i][j].cis[k]][i] = 1;
            }
        }
    }
}
//Função Main
int main (int argc, char *argv[]) {
    static int test_count = 0; //contador de testes
    static int token, event, r, i, j; 
    static char fa_name[5];

    //váriaveis usadas para calcular a rodada atual de teste
    int rodada_atual = 0;
    int old_time = 0;

    //Verifica se o número de argumentos está ok
    if (argc != 4) {
        puts ("Uso correto: ./cisjAssinc <num_processos> <tempo_simulacao> <probabilidade de falha em %>\n");
        puts ("Exemplo: ./cisjAssinc 8 300 10 \n");
        exit(1);
    }
 
   //Insere os argumentos na respectivas variáveis
    n = atoi(argv[1]);
    int simulation_time = atoi(argv[2]);
    int probab = atoi(argv[3]);

    smpl(0, "Trabalho T2 -> vCube Assíncrono");
    reset();
    stream(1);

    //Matriz com info de quem testa quem, i testa j se test[i][j] = 1;
    int test[n][n];

    //inicialização dos nos e eventos
    no = (st_no *) malloc(sizeof(st_no)*n);
    events = (st_event *) malloc(sizeof(st_event)*n);

    //Se na posicao i for igual a 1, quer dizer que o nó não está falho
    info_no = (int *) malloc(sizeof(int)*n);
    for (int i = 0; i < n; i++) {
        info_no[i] = 1;
    }

    for (i = 0; i < n; i++) {
        memset(fa_name,'\0',5);
        sprintf(fa_name,"%d", i);
        no[i].id = facility (fa_name,1);
        no[i].states = (int *) malloc(sizeof(int)*n);
        for (j = 0; j < n; j++) {
            no[i].states[j] = -1; //Unknown
        }
        no[i].states[i] = 0; //Zera o States do próprio processo
    }

    //iniciando a váriavel do número de cluestes
    num_cluster = (int)log2(n);

    //Manda criar a tabela CIS
    st_cis tabela_cis[n][num_cluster];
    criaCIS(tabela_cis);

    //Schedule de eventos
    for (int i = 0; i < n; i++) {
        schedule(TEST, 30.0, i);
    }
//   schedule(FAULT, 100.0, 1);
//   schedule(FAULT, 100.0, 3);
//   schedule(FAULT, 160.0, 5);
//   schedule(FAULT, 300.0, 7);
//   schedule(RECOVERY, 210.0, 1);
//   schedule(RECOVERY, 400.0, 3);
//   schedule(RECOVERY, 300.0, 5);
//   schedule(RECOVERY, 400.0, 7);

    //Gera a matriz de teste
    matrizTeste(n, tabela_cis, test);


    /* agora vem o loop principal do simulador */

    puts("======================================================================================"); 
    puts("Início da execução: Trabalho 2 - vCube Assíncrono.");
    puts("Implementação de um detector de falhas vCube Assíncrono no ambiente de simulação SMPL.");
    puts("Um evento consiste da mudança de estado de um ou mais processos.");
    puts("É exibido o número de testes executados e a latência para todos os processos corretos detectarem o evento.");
    puts("Neste caso os processos podem levantar falsas suspeitas de falhas");
    puts("Cada processo mantém o vetor STATE[0..N-1] de contadores de eventos, inicializado em -1 (estado “unknown”).");
    puts("Aluno: Diogo Bortolini - Disciplina Sistemas Distribuídos");
    puts("======================================================================================\n"); 

    //Loop ocorre até o tempo informado se esgotar
    while (time() <= simulation_time) { 
        cause(&event, &token);
        switch(event) {

            case TEST:
                //se o processo não está falho, faz o teste
                if (status(no[token].id) == 0) {

                    //printa qual é a rodada de testes
                    if (old_time != time()) {
                        rodada_atual += 1 ;
                        old_time = time();
                        printf("\n ###############  RODADA %d ###############\n", rodada_atual);
                    }
                    //realiza o testes programados para o processo i
                    for (i = 0; i < n; i++) {
                        //se tiver teste programado e o status não estiver como falho
                        if (test[token][i] == 1 && (no[token].states[i] % 2 == 0 || no[token].states[i] == -1)) { 
                            n_aleatorio = rand() % 100 + 1;
                            if (status(no[i].id) == 1 || n_aleatorio <= probab) { //se processo está falha ou probab definiu uma falsa suspeita
                                printf("Processo %d testa processo %d com %s no tempo %4.1f", token, i, "FALHA",time());
                                printar = 1; 
                                if(n_aleatorio <= probab && status(no[i].id) == 0) { //caso o no esteja ok, mas foi falsa suspeita
                                    printf(" *** FALSA SUSPEITA ***");
                                    //Recalcula os Testes 
                                    matrizTeste(n, tabela_cis, test);
                                    //criando evento SUSPEITO se já não existe
                                    if (events[i].node_event != 1) {
                                        novoEvento(events, rodada_atual, test_count, i, SUSPECT);
                                    }
                                }
                                //se processo testado retornar falha e a posicao dele no vetor state estiver com um número par, precisa atualizar
                                if (no[token].states[i] == -1) no[token].states[i] = 1; //se ainda está -1 e falhou
                                if (no[token].states[i] % 2 == 0) {
                                    no[token].states[i] += 1;
                                    printf(", Processo %d ATUALIZOU state de [ %d ]\n", token, i);
                                    printar = 1;
                                }
                                else {
                                    printf("\n");
                                }

                                //atualiza contador
                                test_count++;

                                //verifica o diagnóstico do evento
                                for (int i=0; i<n; i++) {
                                    if (events[i].node_event ==1) {
                                        events[i].number_test +=1;
                                        if (atualizaEvento(events, i) == 1) { //Se todos os processos perceberam o evento 
                                            events[i].latencia = rodada_atual - events[i].rodada;
                                            printf("\n**** DADOS DO EVENTO APÓS TODOS PROCESSOS PERCEBEREM ****\n");
                                            imprimirEvento(events, test_count, i); //mostrar dados do evento
                                            limpaEvento(events, i); //Já percebido, então remover dados do evento
                                            printf("*********************************************************\n\n");
                                        }

                                    }
                                }

                            }
                            else {
                                //caso o teste retorne OK
                                printf("Processo %d testa processo %d com %s no tempo %4.1f", token, i,"OK",time());
                                //se processo testado está ok e estiver com um numero impar, que dizer que ele estava falho
                                if (no[token].states[i] % 2 == 1 || no[token].states[i] % 2 == -1) {
                                    no[token].states[i] += 1;
                                    printf(", Processo %d ATUALIZOU state de [ %d ]", token, i);
                                    printar = 1;
                                }

                                //atualiza os States
                                if (atualizaState(token, i) == FALSE) {
                                    printf("\n"); 
                                }
                                //Imprime os States
                                if (printar == 1) {
                                    imprimirState();
                                    printar = 0;
                                }
                                test_count++;

                                //checa se o testador não está falho no testado
                                if ((no[i].states[token] > no[token].states[i]) && (no[i].states[token] > -1))  {
                                    printf ("\n@@@@@@ PROCESSO %d , detectou que foi vítima de FALSA SUSPEITA pelo %d @@@@@@@@ \n",token, i);
				    if (events[token].node_event ==1) {
                                        events[token].latencia = rodada_atual - events[token].rodada;
                                        printf("\n**** DADOS DO EVENTO DEPOIS QUE PROCESSO PERCEBEU QUE FOI VÍTIMA DE FALSA SUSPEITA ****\n");
                                        imprimirEvento(events, test_count, token); //Mostrar dados do evento
                                        limpaEvento(events, token); //Já percebido, então remover os dados do evento
                                        printf("*********************************************************\n\n");
                                    }
                                    r = request(no[token].id, token, 0);
                                    if (r != 0) {
                                        puts ("Não foi possível falhar o processo...");
                                        exit(1);
                                    }
                                    printf("Processo %d FALHOU no tempo %4.1f\n", token, time());

                                    //criando evento
                                    novoEvento(events, rodada_atual, test_count, token, FAULT);

                                    limpaState(token); //Processo falho, coloca State dele com -1 para todos os processos
                                    info_no[token] = 0;

                                    //Recalcula os Testes e imprime as infos do evento ocorrido
                                    matrizTeste(n, tabela_cis, test);
                                    printf("\n**** DADOS NOVO EVENTO ****\n");
                                    imprimirEvento(events, test_count, token); //Mostrar dados do novo evento
                                    printf("***************************\n\n");

                                }

                                //verifica o diagnóstico do evento
                                for (int i=0; i < n; i++) {
                                    if (events[i].node_event ==1) {
                                        if (atualizaEvento(events, i) == 1) { //Se todos os processos perceberam o evento
                                            events[i].latencia = rodada_atual - events[i].rodada;
                                            printf("\n**** DADOS DO EVENTO APÓS TODOS PROCESSOS PERCEBEREM ****\n");
                                            imprimirEvento(events, test_count, i); //Mostrar dados do evento
                                            limpaEvento(events, i); //Já percebido, então remover os dados do evento
                                            printf("*********************************************************\n\n");
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
                schedule(TEST, 30.0, token);
                break;


            case FAULT:
                r = request(no[token].id, token, 0);
                if (r != 0) {
                    puts ("Não foi possível falhar o processo...");
                    exit(1);
                }
                printf("Processo %d FALHOU no tempo %4.1f\n", token, time());

                //criando evento
                novoEvento(events, rodada_atual, test_count, token, FAULT);

                limpaState(token); //Processo falho, coloca State dele com -1 para todos os processos
                info_no[token] = 0;

                //Recalcula os Testes e imprime as infos do evento ocorrido
                matrizTeste(n, tabela_cis, test);
                printf("\n**** DADOS NOVO EVENTO ****\n");
                imprimirEvento(events, test_count, token); //Mostrar dados do novo evento
                printf("***************************\n\n");

            break;

            //------------------------------------------------------------------
            case RECOVERY:
                release(no[token].id, token);

                //criando evento
                novoEvento(events, rodada_atual,  test_count, token, RECOVERY);
                info_no[token] = 1;

                //Recalcula os Testes e imprime as infos do evento ocorrido
                matrizTeste(n, tabela_cis, test);
                printf("\nprocesso %d RECUPEROU no tempo %4.1f\n", token, time());
                printf("\n**** DADOS NOVO EVENTO ****\n");
                imprimirEvento(events, test_count, token); //Mostrar dados do novo evento
                printf("***************************\n\n");
            break;
        }
    }
    free(events);
}
