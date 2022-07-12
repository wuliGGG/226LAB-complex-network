// Prisoners Dilemma game on a small-world graph constructed from a square lattice 
// Some players are blocked to give their strategy (other players cannot adopt their strategy)

// standard include
#include <iostream>
#include <fstream>
#include <cstdlib>
#include <cstdio>
#include <cmath>
#include <ctime>

using namespace std;

// define priority classes
#define NORMAL_PRIORITY_CLASS       0x00000020
#define IDLE_PRIORITY_CLASS         0x00000040
#define HIGH_PRIORITY_CLASS         0x00000080
#define REALTIME_PRIORITY_CLASS     0x00000100

// define parameters
#define L           1000      /* lattice size                   */
#define SIZE        (L*L)    /* number of sites                */
#define MC_STEPS    50000   /* run-time in MCS     */
#define OUT_STEPS    5000   /* Last 5000 steps  */
//#define r               /* temptation to defect */
#define K           0.1      /* temperature */
#define Q           0      /* Q portion of links are rewired */
#define NAMEOUT     "K4b075r5Q2"
#define RANDOMIZE   3145215

double b;
double payoff_matrix[2][2] = 
								 { {1,      0},
								   {b,      0} };
							

#define update_payoff_matrix(b) 		\
		payoff_matrix[1][0] = b         

typedef int       tomb1[SIZE];
typedef long int  tomb3[SIZE][4];
typedef double    tomb4[SIZE];

tomb1 age_up;
tomb1 age_down;
int age_T=20;

 
tomb1 player_s_up;         /* matrix ,containing players strategies */
tomb1 player_s_down; 
tomb3 player_n;         /* matrix, containing players neighbours */

double p[SIZE];	//����RL��һ��������ĺ������� 
double bt= 1;//��
double A =0.5; //����

int cnt_s_up[2];			/* Count strategy: 0 for Cooperator, 1 for defecter */
int cnt_s_down[2];
void prodgraph(void);      /* creates host graph                    */
void initial(void);        /* initial state                         */
double payoff(int x);
void update_up(int x);
void update_down(int x);

//ofstream outfile1;
ofstream outfile2;


//���������������ģ�飬���ù���,ֱ���þ��У���randf()����ֱ�Ӳ���0-1������ȷֲ����������randi(x),����0---x-1���������
/*************************** RNG procedures ****************************************/
#define NN 624
#define MM 397
#define MATRIX_A 0x9908b0df   /* constant vector a */
#define UPPER_MASK 0x80000000 /* most significant w-r bits */
#define LOWER_MASK 0x7fffffff /* least significant r bits */
#define TEMPERING_MASK_B 0x9d2c5680
#define TEMPERING_MASK_C 0xefc60000
#define TEMPERING_SHIFT_U(y)  (y >> 11)
#define TEMPERING_SHIFT_S(y)  (y << 7)
#define TEMPERING_SHIFT_T(y)  (y << 15)
#define TEMPERING_SHIFT_L(y)  (y >> 18)

static unsigned long mt[NN]; /* the array for the state vector  */
static int mti=NN+1; /* mti==NN+1 means mt[NN] is not initialized */
void sgenrand(unsigned long seed)
{int i;
 for (i=0;i<NN;i++) {mt[i] = seed & 0xffff0000; seed = 69069 * seed + 1;
                     mt[i] |= (seed & 0xffff0000) >> 16; seed = 69069 * seed + 1;
  }
  mti = NN;
}
void lsgenrand(unsigned long seed_array[])
{ int i; for (i=0;i<NN;i++) mt[i] = seed_array[i]; mti=NN; }
double genrand() 
{
    unsigned long y;
    static unsigned long mag01[2]={0x0, MATRIX_A};
    if (mti >= NN) 
    {
        int kk;
        if (mti == NN+1) sgenrand(4357); 
        for (kk=0;kk<NN-MM;kk++) {
            y = (mt[kk]&UPPER_MASK)|(mt[kk+1]&LOWER_MASK);
            mt[kk] = mt[kk+MM] ^ (y >> 1) ^ mag01[y & 0x1];
        }
        for (;kk<NN-1;kk++) {
            y = (mt[kk]&UPPER_MASK)|(mt[kk+1]&LOWER_MASK);
            mt[kk] = mt[kk+(MM-NN)] ^ (y >> 1) ^ mag01[y & 0x1];
        }
        y = (mt[NN-1]&UPPER_MASK)|(mt[0]&LOWER_MASK);
        mt[NN-1] = mt[MM-1] ^ (y >> 1) ^ mag01[y & 0x1];
        mti = 0;
    }  
    y = mt[mti++]; y ^= TEMPERING_SHIFT_U(y); y ^= TEMPERING_SHIFT_S(y) & TEMPERING_MASK_B;
    y ^= TEMPERING_SHIFT_T(y) & TEMPERING_MASK_C; y ^= TEMPERING_SHIFT_L(y);
    return y;  
}

double randf(){ return ( (double)genrand() * 2.3283064370807974e-10 ); }
long randi(unsigned long LIM){ return((unsigned long)genrand() % LIM); }

/********************** END of RNG ************************************/


void initial(void)
{
	cnt_s_up[0] = cnt_s_up[1] = 0;
	cnt_s_down[0] = cnt_s_down[1] = 0;
	
	for (int i=0; i<SIZE; i++)
	{
		
		player_s_up[i] = randi(2);
		player_s_down[i] = randi(2);
		
		age_up[i] = age_down[i]=1;

		cnt_s_up[player_s_up[i]]++;
		cnt_s_down[player_s_down[i]]++;
		
		p[i] = 0.5;
	}
}

// creates first a square grid graph and then rewires Q links 
void prodgraph(void){
	int nneighbor, iu, ju, neighbor1, neighbor2;
	long int rewire, first, player1,player2,player3,MCe;
	double x;
	int i,j;
   
	// set up an initial square lattice
	for(i=0; i<L; i++)                     
	{
		for(j=0; j<L; j++)
		{ 
			// the first player
			player1 = L * j + i;             

			// and its four nearest neighbors
			iu = i + 1;         
			ju = j;     
			if (iu==L) iu = 0;
			player2 = L * ju + iu;  
			player_n[player1][0] = player2;

			iu = i;             
			ju = j + 1; 
			if (ju==L) ju = 0;
			player2 = L * ju + iu;  
			player_n[player1][1] = player2;

			iu = i - 1;         
			ju = j;     
			if (i==0) iu = L - 1;
			player2 = L * ju + iu;  
			player_n[player1][2] = player2;

			iu = i;             
			ju = j - 1; 
			if (j==0) ju = L - 1;
			player2 = L * ju + iu;  
			player_n[player1][3] = player2;
		}
	}
}


double payoff_up(int x){//�ϲ�������� 
	double pay = 0;
	for (int i = 0; i < 4; i++)
		pay += payoff_matrix [player_s_up[x]] [player_s_up[player_n[x][i]]];
	return pay;
}
double payoff_down(int x){//�²�������� 
	double pay = 0;
	for (int i = 0; i < 4; i++)
		pay += payoff_matrix [player_s_down[x]] [player_s_down[player_n[x][i]]];
	return pay;
}



double fitness_up(int x)
{
	if(age_up[x]>=age_T)
		return 0.5*payoff_down(x)+payoff_up(x);
	else
		return payoff_up(x);
}
 

double stimu(int x)
{
	double s, r;
	r = payoff_up(x) / 4;
	s = tanh(bt * (r - A));
	return s;
}

//����x���²��Եĸ��� 
void calcul(int x)
{
	int i, j; double s;
	i=x;
	s = stimu(i);
	if ((s >= 0) && player_s_up[i]== 0)
	{
		p[i] = p[i] + (1 - p[i]) * s;
	}
	else if ((s < 0) && player_s_up[i] == 0)
	{
		p[i] = p[i] + p[i] * s;
	}
	else if ((s >= 0) && player_s_up[i] == 1)
	{
		p[i] = p[i] - p[i] * s;
	}
	else
	{
		p[i] = p[i]- (1 - p[i]) * s;
	}
}



double fitness_down(int x)
{
	if(age_down[x]>=age_T)
		return 0.5*payoff_up(x)+payoff_down(x);
	else
		return payoff_down(x);
}

//�ϲ���Ը��£�RL
 
/* 
void update_up(int x)
{
    int y; 
 	double prob_up = 0;	// Probability of updating, initial not update
	y = player_n[x][int(randi(4))];
	if(player_s_up[x] != player_s_up[y])
	{
		prob_up = 1/(1+exp((fitness_up(x) - fitness_up(y))/K));

		if (randf() < prob_up)
		{
			cnt_s_up[player_s_up[x]]--;	// Old strategy
			player_s_up[x] =  player_s_up[y];
			cnt_s_up[player_s_up[x]]++;	// New strategy
			
			age_up[x] = 1;
		}
		else
		{
			if(age_up[x] <=99)  age_up[x] ++;
			else                age_up[x] = 1;
		}
	}
	else
	{
	    if(age_up[x] <= 99)   age_up[x] ++;
		else                  age_up[x] = 1;
	}
}
*/

void update_up(int x) {
	calcul(x);
	if (randf() <= p[x])
	{
		cnt_s_up[player_s_up[x]]--;
		player_s_up[x] = 0;
		cnt_s_up[player_s_up[x]]++;
	}
	else
	{
		cnt_s_up[player_s_up[x]]--;
		player_s_up[x] = 1;
		cnt_s_up[player_s_up[x]]++;
	}

	return;
}

void update_down(int x)
{
    int y; 
 	double prob_down = 0;	// Probability of updating, initial not update
	y = player_n[x][int(randi(4))];
	if(player_s_down[x] != player_s_down[y])
	{
		prob_down = 1/(1+exp((fitness_down(x) - fitness_down(y))/K));

		if (randf() < prob_down)
		{
			cnt_s_down[player_s_down[x]]--;	// Old strategy
			player_s_down[x] =  player_s_down[y];
			cnt_s_down[player_s_down[x]]++;	// New strategy
			
			age_down[x] = 1; 
		}
		else
		{
			if(age_down[x] <= 99)   age_down[x] ++;
			else                    age_down[x] = 1;
		}
	}
	else
	{
		if(age_down[x] <= 99)       age_down[x] ++;
		else                        age_down[x] = 1;
	}
}


void game(void)
{
	for(int i=0;i<SIZE;i++)
	{
		int x = randi(SIZE);
		update_up(x);
		update_down(x);
		
   }
}


// the main program
int main()
{
	int steps;
    double fc_up,fc_down, last_sum_up,last_sum_down, avg_fc_up,avg_fc_down;

	//outfile1.open("frequency.txt");
	outfile2.open("average.txt");

   
	if(!outfile2){
	 cout<<"can not open";
	 abort();
	}
	// initialize the random number generation
	sgenrand(RANDOMIZE);
	prodgraph();

for(b = 1; b <= 2; b += 0.1)
	{	
	    avg_fc_up=0;
	    last_sum_up=0;
		avg_fc_down=0;
	    last_sum_down=0; 
	    update_payoff_matrix(b);
		initial();
		
		char frequency[100];
		sprintf(frequency,"%g_frequency.txt",b);
		FILE* outfile1=fopen(frequency,"w");
		
		for (steps=0; steps<MC_STEPS; steps++)
		{
			game();
	        fc_up=(double)cnt_s_up[0]/SIZE;	// OLD: tongji()
	        fc_down=(double)cnt_s_down[0]/SIZE;
		    //outfile1<<steps<<'\t'<<fc_up<<'\t'<<fc_down<<endl;	// Output: frequency
	        fprintf(outfile1,"%d\t%lf\t%lf\n",steps,fc_up,fc_down);
			if(steps > MC_STEPS - OUT_STEPS - 1)
			    {
				   last_sum_up += fc_up;
				   last_sum_down += fc_down;
				}
	    }
		avg_fc_up = (double)last_sum_up/OUT_STEPS;
		avg_fc_down = (double)last_sum_down/OUT_STEPS;
	
	    cout<<b<<"\t"<< age_T<<"\t"<<avg_fc_up<<'\t'<<avg_fc_down<<endl;
	  	outfile2<<b<<"\t"<<age_T<<"\t"<< avg_fc_up<<'\t'<<avg_fc_down<<endl;
		if(fabs(avg_fc_down) < 1e-7||fabs(avg_fc_down) < 1e-7) break;
		
		//outfile1.close();
		fclose(outfile1);
	}
	
	
	outfile2.close();
	
	return 0;
}

