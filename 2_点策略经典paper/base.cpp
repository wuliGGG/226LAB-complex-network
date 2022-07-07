#include<stdio.h>
#include<stdlib.h>
#include<math.h>

/* Random function */
#define NN 624
#define MM 397
#define MATRIX_A 0x9908b0df          /* constant vector a */
#define UPPER_MASK 0x80000000        /* most significant w-r bits */
#define LOWER_MASK 0x7fffffff        /* least significant r bits */
#define TEMPERING_MASK_B 0x9d2c5680
#define TEMPERING_MASK_C 0xefc60000
#define NAMEOUT     "K4b075r5Q2"
#define TEMPERING_SHIFT_U(y)  (y >> 11)
#define TEMPERING_SHIFT_S(y)  (y << 7)
#define TEMPERING_SHIFT_T(y)  (y << 15)
#define TEMPERING_SHIFT_L(y)  (y >> 18)
static unsigned long mt[NN];        /* the array for the state vector  */
static int mti = NN + 1;            /* mti==NN+1 means mt[NN] is not initialized */
void sgenrand(unsigned long seed) {
	int i;
	for (i = 0; i < NN; i++) {
		mt[i] = seed & 0xffff0000; seed = 69069 * seed + 1;
		mt[i] |= (seed & 0xffff0000) >> 16; seed = 69069 * seed + 1;
	}
	mti = NN;
}
void lsgenrand(unsigned long seed_array[]) {
	int i; for (i = 0; i < NN; i++) mt[i] = seed_array[i]; mti = NN;
}
double genrand() {
	unsigned long y;
	static unsigned long mag01[2] = { 0x0, MATRIX_A };
	if (mti >= NN)
	{
		int kk;
		if (mti == NN + 1) sgenrand(4357);
		for (kk = 0; kk < NN - MM; kk++) {
			y = (mt[kk] & UPPER_MASK) | (mt[kk + 1] & LOWER_MASK);
			mt[kk] = mt[kk + MM] ^ (y >> 1) ^ mag01[y & 0x1];
		}
		for (; kk < NN - 1; kk++) {
			y = (mt[kk] & UPPER_MASK) | (mt[kk + 1] & LOWER_MASK);
			mt[kk] = mt[kk + (MM - NN)] ^ (y >> 1) ^ mag01[y & 0x1];
		}
		y = (mt[NN - 1] & UPPER_MASK) | (mt[0] & LOWER_MASK);
		mt[NN - 1] = mt[MM - 1] ^ (y >> 1) ^ mag01[y & 0x1];
		mti = 0;
	}
	y = mt[mti++]; y ^= TEMPERING_SHIFT_U(y); y ^= TEMPERING_SHIFT_S(y) & TEMPERING_MASK_B;
	y ^= TEMPERING_SHIFT_T(y) & TEMPERING_MASK_C; y ^= TEMPERING_SHIFT_L(y);
	return y;
}
double randf() { return ((double)genrand() * 2.3283064370807974e-10); }
long randi(unsigned long LIM) { return((unsigned long)genrand() % LIM); }
/* End of random */

#define RANDOMIZE 3145215
#define L 100
#define K 0.1
#define NEINUM 4
#define SIZE (L*L)
#define MC_STEPS 10000
#define REC_STEPS 5000
#define REFRESH_PRE 100	 /* Control the frequency of refresh screen, 1 for all the time */
#define TRY_TIME 10
double b; 
int net[SIZE][4];	 /* Control the frequency of refresh screen, 1 for all the time */
char stra[SIZE];	
int cooperator,defector;
char frequency[100];
/* Payoff matrix and its update */
double payoff_matrix[2][2] = { {1,0},
							   {1,0} };
/* Call update_matrix(b) after loop for b */
#define update_matrix(b) payoff_matrix[1][0]=b;

//player x周围的四个邻居
void prod_neighbors() {
	int i, j, x;
	for (i = 0; i < L; i++) {
		for (j = 0; j < L; j++) {
			x = i * L + j;
			net[x][0] = i * L + ((j - 1 + L) % L);	/*left*/
			net[x][1] = ((i - 1 + L) % L)*L + j;	/*up*/
			net[x][2] = ((i + 1) % L)*L + j;	/*down*/
			net[x][3] = i * L + ((j + 1) % L);	/*right*/
		}
	}
}

//对每个player进行策略初始化
void init() {
	cooperator=defector=0;
	int i;
	for (i = 0; i < SIZE; i++){
		stra[i] = randi(2);		//随机生成0,1
		if(stra[i]==0)
			cooperator++;
		else
			defector++;
	}		
}

double payoff(int x) {
	int i;
	double pay = 0;
	for (i = 0; i < NEINUM; i++)
		pay += payoff_matrix[stra[x]][stra[net[x][i]]];		//与自己的邻居进行对比，算出收益
	return pay;
}

void update_stra(){
	int i,j,player;
	double pay1,pay2;
	for(i=0;i<SIZE;i++){
		player=(int)randi(SIZE);
		pay1=payoff(player);
		j=net[player][(int)randi(NEINUM)];			//player的一个邻居
		pay2=payoff(j);
		if(stra[player] != stra[j]){
			if(randf() < 1 / (1 + exp((pay1 - pay2) / K))){
				stra[player]=stra[j];
			}
		}
    }
	return;
}

void update_data(){
	int i;
	cooperator=defector=0;
	for(i=0;i<SIZE;i++){
		if(stra[i]==0)
			cooperator++;
		else
			defector++;
	}
	return; 
}

int main()
{
	
sgenrand(RANDOMIZE);
	prod_neighbors();
	int x, step;
	double fc, afc = 0;

	FILE*fp_aver = fopen("average.txt", "w");
	for(b=1;b<1.1;b+=0.05){
		
		sprintf(frequency,"%g_frequency.txt",b);
		FILE*fp_freq = fopen(frequency, "w");
		update_matrix(b);
		init();
		for (step = 1; step < MC_STEPS; step++) {		
			update_stra();
			update_data();
			fc = (double)cooperator/SIZE;
			if (step > MC_STEPS - REC_STEPS - 1)	//排除干扰
				afc += fc;
			fprintf(fp_freq, "%d\t%lf\n", step, fc);
			if (step%REFRESH_PRE == 0)
				printf("\rStep:%d\tC:%lf%%		", step, fc * 100);
			if ((!cooperator) || (!defector)) {		//当只剩下C或只剩下D时终止程序
				if (step++ < MC_STEPS - REC_STEPS) afc = cooperator ? 1 : 0;
				break;
			}
		}
		if (step > MC_STEPS - REC_STEPS)
			afc /= step + REC_STEPS - MC_STEPS;
		fprintf(fp_aver, "%g\t%g\n", b, afc);
		printf("\rb: %lf\tavg_C: %lf%%               ",b, afc * 100);
		putchar(10);
		fclose(fp_freq);
	}

	fclose(fp_aver);

	return 0;
}


