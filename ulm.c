/*--------------------------------------------------------
Implementation of the ULM in the ATP    
Ms. Felipe O. S. Zanon - UFMG  
Dr. Osis E. S. Leal - UTFPR     
Dr. Alberto De Conti - UFMG 
Federal University of Minas Gerais - (UFMG) 
Federal University of Technology - Parana (UTFPR)
--------------------------------------------------------*/

#include <stdio.h>
#include <stdlib.h>
#include <complex.h>
#include <string.h>
#include <math.h>

//Declaration of Variables:

double *ikATP; //current at k terminal read from ATP
double *imATP; //current at m terminal read from ATP

_Complex double *vkATP; //input voltage from ATP k terminal
_Complex double *vkATPold; //input voltage from ATP (a previous time step) k terminal
_Complex double *vmATP; //input voltage from ATP at m terminal
_Complex double *vmATPold; //input voltage from ATP (a previous time step) m terminal

double *ikHist; //historical current at k terminal
double *imHist; //historical current at m terminal

int nPhase,nMode,nPoleYc,nPoleH; //number of phases, modes, Yc poles, H poles
int bufferSize; //maximum buffer size
int *taus; //vector of time delays

//Poles and residues of Yc and H
_Complex double *poleYc;
_Complex double ***resYc;
_Complex double *poleH;
_Complex double ****resH;

_Complex double **resid0Yc; //residue0 of Yc
_Complex double **Gulm; //conductances of the ULM equivalent circuit 

_Complex double **jkn;
_Complex double **jmn;
_Complex double **sumrnYc;
_Complex double *pnYcvet;
_Complex double ***rnYc;

_Complex double ***bkij;
_Complex double ***bmij;
_Complex double ***sumrnA;
_Complex double *pnAvet;
_Complex double ****rnA;

_Complex double *jkhP; //partial result of matrix multiplication jkh
_Complex double *jkhQ; //partial result of matrix multiplication jkh
_Complex double *jmhP; //partial result of matrix multiplication jmh
_Complex double *jmhQ; //partial result of matrix multiplication jmh

_Complex double **jknP; //partial result of matrix multiplication jkn
_Complex double **jknQ; //partial result of matrix multiplication jkn
_Complex double **jmnP; //partial result of matrix multiplication jkn
_Complex double **jmnQ; //partial result of matrix multiplication jkn

_Complex double *bkP; //Term of bk=bkP+bkQ
_Complex double *bkQ; //Term of bk=bkP+bkQ
_Complex double *bk; //Sum of bk=bkP+bkQ
_Complex double ***bkijP; //bkijP=pnAvet*bkij
_Complex double ***bkijQ; //bkijQ=rnA*(fmTauIntp+fmTauIntpAnt)
_Complex double *bkold; //Sum of bk=bkP+bkQ

_Complex double *bmP; 
_Complex double *bmQ; 
_Complex double *bm; 
_Complex double ***bmijP; 
_Complex double ***bmijQ; 
_Complex double *bmold; 

int *aux; //auxiliary variable to access the buffer according to the mode
double deltaT; //time step of simulation imported from ATP
double *tauDisc;
double *tauOtim;
double *tauInt;
double *tauDec;
double *bufferTau;

double *weight1; //Weight 1 for linear interpolation
double *weight2; //Weight 2 for linear interpolation

_Complex double **fmBuffer; //buffer of fm
_Complex double **fkBuffer; //buffer of fm

_Complex double **fmTauIntp; //fm interpolated 
_Complex double **fmTauIntpAnt; //fm interpolated (a previous time step)
_Complex double **fkTauIntp; //fk interpolated  
_Complex double **fkTauIntpAnt; //fk interpolated (a previous time step)

//*********************************************************************************

void c_ulm_m__(double xdata_ar[],
				double xin_ar[],
				double xout_ar[],
				double xvar_ar[])
{ 
	int ii,j,k,mm;
	
	//vkATPold=vkATP
	for (ii = 0; ii < nPhase; ii++){
		vkATPold[ii]=vkATP[ii];
		vmATPold[ii]=vmATP[ii];
    }		
	//Import voltage and current from ATP
	  for (ii=0; ii<nPhase; ii++)
      { 
		vkATP[ii] = xin_ar[ii];
      }
	  for (ii=nPhase; ii<2*nPhase; ii++)
      { 
		ikATP[ii-nPhase] = xin_ar[ii];
      }
	  
	  for (ii=2*nPhase; ii<3*nPhase; ii++)
      { 
		vmATP[ii-2*nPhase] = xin_ar[ii];
      }
	  
	  for (ii=3*nPhase; ii<4*nPhase; ii++)
      { 
		imATP[ii-3*nPhase] = xin_ar[ii];
      }	
	
	//Linear Interpolation of fm, fk
	for (j = 0; j < nPhase; j++){
		for (ii = 0; ii < nPhase; ii++){
			fmTauIntp   [ii][j]=weight1[j]*fmBuffer[ii][2+aux[j]]+weight2[j]*fmBuffer[ii][1+aux[j]];
			fmTauIntpAnt[ii][j]=weight1[j]*fmBuffer[ii][1+aux[j]]+weight2[j]*fmBuffer[ii][0+aux[j]];
			fkTauIntp   [ii][j]=weight1[j]*fkBuffer[ii][2+aux[j]]+weight2[j]*fkBuffer[ii][1+aux[j]];
			fkTauIntpAnt[ii][j]=weight1[j]*fkBuffer[ii][1+aux[j]]+weight2[j]*fkBuffer[ii][0+aux[j]];					
		}
    }
	
	//Zerar bkQ
	for (ii = 0; ii < nPhase; ii++){
		bkQ[ii]=0+0*I;
		bmQ[ii]=0+0*I;
	}
	//bkQ=sumrnA*(fmTauIntp+fmTauIntpAnt)
	for (k = 0; k < nMode; k++){
		for (ii = 0; ii < nPhase; ii++){
			for (j = 0; j < nPhase; j++){
				bkQ[ii] += sumrnA[ii][j][k]*(fmTauIntp[j][k]+fmTauIntpAnt[j][k]);
				bmQ[ii] += sumrnA[ii][j][k]*(fkTauIntp[j][k]+fkTauIntpAnt[j][k]);
			}
		}			
    }
	//bkP=0
	for (ii = 0; ii < nPhase; ii++){
		bkP[ii]=0;
		bmP[ii]=0;
	}
	//bkP=pnAvet*bkij
	for (ii = 0; ii < (nPhase); ii++){
		for (j = 0; j < (nMode); j++){
			for (k = 0; k < (nPoleH); k++){
				bkP[ii] += pnAvet[k]*bkij[ii][k][j];
				bmP[ii] += pnAvet[k]*bmij[ii][k][j];
			}
		}	
    }		
	//bkold=bk
	for (ii = 0; ii < nPhase; ii++){
		bkold[ii]=bk[ii];
		bmold[ii]=bm[ii];
    }	
	//bk=bkP+bkQ
	for (ii = 0; ii < nPhase; ii++){
		bk[ii]=bkP[ii]+bkQ[ii];
		bm[ii]=bmP[ii]+bmQ[ii];
    }	
	//bkijP=pnAvet*bkij
	for (j = 0; j < (nMode); j++){
		for (k = 0; k < (nPoleH); k++){
			for (ii = 0; ii < (nPhase); ii++){
				bkijP[ii][k][j] = pnAvet[k]*bkij[ii][k][j];
				bmijP[ii][k][j] = pnAvet[k]*bmij[ii][k][j];
			}
		}
	}		
	//bkijQ=0
	for (j = 0; j < (nMode); j++){
		for (k = 0; k < (nPoleH); k++){
			for (ii = 0; ii < (nPhase); ii++){
				bkijQ[ii][k][j]=0+0*I;
				bmijQ[ii][k][j]=0+0*I;
			}
		}
    }	
	//bkijQ=rnA*(fmTauIntp+fmTauIntpAnt)
	for (j = 0; j < (nMode); j++){
		for (k = 0; k < (nPoleH); k++){
			for (ii = 0; ii < (nPhase); ii++){
				for (mm = 0; mm < (nPhase); mm++){
					bkijQ[ii][k][j] += rnA[ii][mm][k][j]*(fmTauIntp[mm][j]+fmTauIntpAnt[mm][j]);
					bmijQ[ii][k][j] += rnA[ii][mm][k][j]*(fkTauIntp[mm][j]+fkTauIntpAnt[mm][j]);
				}
			}
		}
    }	
	//bkij=bkijP+bkijQ
	for (j = 0; j < (nMode); j++){
		for (k = 0; k < (nPoleH); k++){
			for (ii = 0; ii < (nPhase); ii++){
				bkij[ii][k][j]=bkijP[ii][k][j]+bkijQ[ii][k][j];
				bmij[ii][k][j]=bmijP[ii][k][j]+bmijQ[ii][k][j];
			}
		}
    }		
	//jknP=pnYcvet*jkn
	for (k = 0; k < (nPoleYc); k++){
		for (ii = 0; ii < (nPhase); ii++){
			jknP[ii][k] = pnYcvet[k]*jkn[ii][k];
			jmnP[ii][k] = pnYcvet[k]*jmn[ii][k];
		}
	}	
	//jknQ=rnYc*(vkATP+vkATPold)
	for (k = 0; k < (nPoleYc); k++){
		for (ii = 0; ii < (nPhase); ii++){
			jknQ[ii][k]=0+0*I;
			jmnQ[ii][k]=0+0*I;
		}		
    }	
	//jknQ=rnYc*(vkATP+vkATPold)
	for (k = 0; k < (nPoleYc); k++){
		for (ii = 0; ii < (nPhase); ii++){
			for (mm = 0; mm < (nPhase); mm++){
				jknQ[ii][k] += rnYc[ii][mm][k]*(vkATP[mm]+vkATPold[mm]);
				jmnQ[ii][k] += rnYc[ii][mm][k]*(vmATP[mm]+vmATPold[mm]);
			}
		}
	}		
	//jkn=jknP+jknQ
	for (ii = 0; ii < nPhase; ii++){
		for (k = 0; k < (nPoleYc); k++){
			jkn[ii][k]=jknP[ii][k]+jknQ[ii][k];
			jmn[ii][k]=jmnP[ii][k]+jmnQ[ii][k];
		}
	}
	//jkhP=0
	for (ii = 0; ii < nPhase; ii++){
		jkhP[ii]=0+0*I;
		jmhP[ii]=0+0*I;
	}	
	//jkhP=pnYcvet*jkn
	for (ii = 0; ii < nPhase; ii++){
		for (k = 0; k < (nPoleYc); k++){
			jkhP[ii] += pnYcvet[k]*jkn[ii][k];
			jmhP[ii] += pnYcvet[k]*jmn[ii][k];
		}	
    }
	//jkhQ=sumrnYc*vkATP
	for (ii = 0; ii < (nPhase); ii++){
		for (mm = 0; mm < nPhase; mm++){
			jkhQ[ii]=0+0*I;
			jmhQ[ii]=0+0*I;
		}	
	}
	//jkhQ=sumrnYc*vkATP
	for (ii = 0; ii < (nPhase); ii++){
		jkhQ[ii]=0;
		jmhQ[ii]=0;
		for (mm = 0; mm < nPhase; mm++){
			jkhQ[ii] += sumrnYc[ii][mm]*vkATP[mm];
			jmhQ[ii] += sumrnYc[ii][mm]*vmATP[mm];
		}	
	}	
	//Move buffer elements one position up
	for (ii = 0; ii < (nPhase); ii++){
		for (k = 0; k < (bufferSize-1); k++){
			fmBuffer[ii][k]=fmBuffer[ii][k+1];
			fkBuffer[ii][k]=fkBuffer[ii][k+1];
		}
	}	
	for (ii = 0; ii < (nPhase); ii++){
		k=bufferSize-1;
		fmBuffer[ii][k]=2*imATP[ii]+bmold[ii];
		fkBuffer[ii][k]=2*ikATP[ii]+bkold[ii];
	}	
	//ikHist=jkhP+jkhQ+bk
	for (ii = 0; ii < (nPhase); ii++){
		ikHist[ii]=bk[ii]-jkhP[ii]-jkhQ[ii];
		imHist[ii]=bm[ii]-jmhP[ii]-jmhQ[ii];
    }
	
	//Export ikHist,imHist to ATP	
	for (ii=0; ii<nPhase; ii++)
	{
	xout_ar[ii] = ikHist[ii];
	}

	for (ii=nPhase; ii<2*nPhase; ii++)
	{
	xout_ar[ii] = imHist[ii-nPhase];
	}	
	return;
}

//***************************************************************************
        
void c_ulm_i__(double xdata_ar[],
				double xin_ar[],
				double xout_ar[],
				double xvar_ar[])
{
	printf("# --------------------------------------------------------\n");
	printf("# Implementation of the Universal Line Model in the Alternative Transients Program\n");
	printf("#     Ms. Felipe O. S. Zanon - UFMG\n");
	printf("#     Dr. Osis E. S. Leal - UTFPR \n");
	printf("#     Dr. Alberto De Conti - UFMG\n");
	printf("# Federal University of Minas Gerais - (UFMG)\n");
	printf("# Federal University of Technology - Parana (UTFPR)\n");
	printf("# --------------------------------------------------------\n");
	
	int ii,j,k,mm;
	float re;
	float im;
	FILE *hFile;
	hFile = fopen("fitULM.txt", "r"); //text file from C:\ATP\atpdraw\work
	if (hFile == NULL)
	{
		printf("FILE NOT FOUND\n");
	}
    //import information from text file
	else
	{
		fscanf(hFile,"%d",&nPhase);
		fscanf(hFile,"%d",&nMode);
		fscanf(hFile,"%d",&nPoleYc);
		fscanf(hFile,"%d",&nPoleH);
	}
//***************************************************************************************

//Variables allocation/initialization:	
	//allocation jkn
	jkn = (_Complex double **) malloc((nPhase) * sizeof(_Complex double*));
	jmn = (_Complex double **) malloc((nPhase) * sizeof(_Complex double*));
	for (ii = 0; ii < nPhase; ii++){
	   jkn[ii] = (_Complex double*) malloc((nPoleYc) * sizeof(_Complex double));
	   jmn[ii] = (_Complex double*) malloc((nPoleYc) * sizeof(_Complex double));
	}
	
	//initialization jkn
	for (k=0;k<(nPoleYc);k++){
		for (ii=0;ii<(nPhase);ii++){
			jkn[ii][k] = 0 + 0 * I;
			jmn[ii][k] = 0 + 0 * I;
		}
	}
	//allocation sumrnYc
	sumrnYc = (_Complex double **) malloc(nPhase * sizeof(_Complex double*));
	for (ii = 0; ii < nPhase; ii++){
	   sumrnYc[ii] = (_Complex double*) malloc(nPhase * sizeof(_Complex double));
	}
	
	//allocation poleYc
	poleYc = (_Complex double *) malloc((nPoleYc) * sizeof(_Complex double));	
	//allocation pnYcvet
	pnYcvet = (_Complex double *) malloc((nPoleYc) * sizeof(_Complex double));
	
	//allocation 3D-matrix resYc
	resYc = (_Complex double ***) malloc((nPhase) * sizeof(_Complex double**));
	for (ii = 0; ii < (nPhase); ii++){
	   resYc[ii] = (_Complex double**) malloc(nPhase * sizeof(_Complex double*));
	   for (k = 0; k < (nPhase); k++){
		   resYc[ii][k] = (_Complex double*) malloc(nPoleYc * sizeof(_Complex double));
	   }
	}	
	
	//allocation 3D-matrix rnYc
	rnYc = (_Complex double ***) malloc((nPhase) * sizeof(_Complex double**));
	for (ii = 0; ii < (nPhase); ii++){
	   rnYc[ii] = (_Complex double**) malloc(nPhase * sizeof(_Complex double*));
	   for (k = 0; k < (nPhase); k++){
		   rnYc[ii][k] = (_Complex double*) malloc(nPoleYc * sizeof(_Complex double));
	   }
	}
	
	//allocation 3D-matrix bkij, bmij
	bkij = (_Complex double ***) malloc((nPhase) * sizeof(_Complex double**));
	bmij = (_Complex double ***) malloc((nPhase) * sizeof(_Complex double**));
	for (ii = 0; ii < (nPhase); ii++){
	   bkij[ii] = (_Complex double**) malloc((nPoleH) * sizeof(_Complex double*));	
	   bmij[ii] = (_Complex double**) malloc((nPoleH) * sizeof(_Complex double*));	
	   for (j = 0; j < (nPoleH); j++){
		   bkij[ii][j] = (_Complex double*) malloc((nMode) * sizeof(_Complex double));	
		   bmij[ii][j] = (_Complex double*) malloc((nMode) * sizeof(_Complex double));	
	   }
	}		
	//initialization bkij, bmij
	for (j=0; j <(nMode);j++){
		for (ii=0; ii <(nPhase);ii++){
			for (k=0; k <(nPoleH);k++){
				bkij[ii][k][j] = 0 + 0 * I;
				bmij[ii][k][j] = 0 + 0 * I;
			}
		}
	}	
	//allocation sumrnA
	sumrnA = (_Complex double ***) malloc((nPhase) * sizeof(_Complex double**));
	for (ii = 0; ii < nPhase; ii++){
	   sumrnA[ii] = (_Complex double**) malloc((nPhase) * sizeof(_Complex double*));
		for (j = 0; j < nPhase; j++){
			sumrnA[ii][j] = (_Complex double*) malloc((nMode) * sizeof(_Complex double));
		}
	}	

	//allocation poleH
	poleH = (_Complex double *) malloc((nPoleH) * sizeof(_Complex double));	
	//allocation pnAvet
	pnAvet = (_Complex double *) malloc((nPoleH) * sizeof(_Complex double));
	
	//allocation 4D-matrix resH
	resH = (_Complex double ****) malloc((nPhase) * sizeof(_Complex double***));
	for (ii = 0; ii < (nPhase); ii++){
		resH[ii] = (_Complex double***) malloc((nPhase) * sizeof(_Complex double**));
		for (j = 0; j < (nPhase); j++){
			resH[ii][j] = (_Complex double**) malloc((nPoleH) * sizeof(_Complex double*));
			for (k = 0; k < (nPoleH); k++){
				resH[ii][j][k] = (_Complex double*) malloc((nMode) * sizeof(_Complex double));
			}
		}
	}	

	//allocation 4D-matrix rnA
	rnA = (_Complex double ****) malloc((nPhase) * sizeof(_Complex double***));
	for (ii = 0; ii < (nPhase); ii++){
		rnA[ii] = (_Complex double***) malloc((nPhase) * sizeof(_Complex double**));
		for (j = 0; j < (nPhase); j++){
			rnA[ii][j] = (_Complex double**) malloc((nPoleH) * sizeof(_Complex double*));
			for (k = 0; k < (nPoleH); k++){
				rnA[ii][j][k] = (_Complex double*) malloc((nMode) * sizeof(_Complex double));
			}
		}
	}  

	//allocation taus,weight1,weight2, tauOtim
	taus = (int *) malloc((nPhase) * sizeof(int));	
	weight1 = (double *) malloc((nPhase) * sizeof(double));
	weight2 = (double *) malloc((nPhase) * sizeof(double));
	tauOtim = (double *) malloc((nPhase) * sizeof(double));

	//allocation resid0Yc, Gulm
	resid0Yc = (_Complex double **) malloc((nPhase) * sizeof(_Complex double*));
	Gulm = (_Complex double **) malloc((nPhase) * sizeof(_Complex double*));
	for (ii = 0; ii < (nPhase); ii++){
		resid0Yc[ii] = (_Complex double*) malloc((nPhase) * sizeof(_Complex double));
		Gulm[ii] = (_Complex double*) malloc((nPhase) * sizeof(_Complex double));	   
	}	

//****************************************************************************************
	
//Import information from text file
	for (ii=0;ii<(nPoleYc);ii++)
	{
		fscanf(hFile,"%f \t %f",&re,&im);
		poleYc[ii] = re + im * I;
	}

	for (k=0;k<(nPoleYc);k++){
		for (ii=0;ii<nPhase;ii++){
			for (mm=0;mm<nPhase;mm++){
				fscanf(hFile,"%f \t %f",&re,&im);
				resYc[ii][mm][k] = re + im * I;
			}
		}
	}
	
	for (ii=0;ii<(nPoleH);ii++)
	{
		fscanf(hFile,"%f \t %f",&re,&im);
		poleH[ii] = re + im * I;
	}
	
	for (j=0;j<(nMode);j++){
		for (k=0;k<(nPoleH);k++){
			for (ii=0;ii<(nPhase);ii++){
				for (mm=0;mm<(nPhase);mm++){
					fscanf(hFile,"%f \t %f",&re,&im);
					resH[ii][mm][k][j] = re + im * I;
				}
			}
		}
	}
	
	for (j=0;j<(nPhase);j++){
		fscanf(hFile,"%f",&re);
		tauOtim[j]=re;
	}
	
	for (j=0;j<(nMode);j++){
		for (ii=0;ii<(nPhase);ii++){
			fscanf(hFile,"%f \t %f",&re,&im);
			resid0Yc[ii][j] = re + im * I;
		}
	}	
	fclose(hFile);
//*************************************************************	

//Variables allocation/initialization:	
	//allocation
	tauDisc = (double *) malloc((nPhase) * sizeof(double));
	tauInt = (double *) malloc((nPhase) * sizeof(double));
	tauDec = (double *) malloc((nPhase) * sizeof(double));
	bufferTau = (double *) malloc((nPhase) * sizeof(double));
	
	//Import time step from ATP
	deltaT = xdata_ar[0];
	
    //Weight calculation for linear interpolation	
	for (ii=0; ii<nPhase; ii++){ 
		re=tauOtim[ii];
		tauDisc[ii]=re/deltaT;
		re=tauDisc[ii];
		tauInt[ii]=(int)re;
		tauDec[ii]=tauDisc[ii]-tauInt[ii];
		bufferTau[ii]=tauInt[ii]+1;
		weight1[ii]=1-tauDec[ii];
		weight2[ii]=tauDec[ii];
	}
	//Find the largest buffer size
	bufferSize=0;
	for (ii=0; ii<nPhase; ii++){ 
		if (bufferTau[ii]>bufferSize){
			re=bufferTau[ii];
			bufferSize = (int)re;
		}
	}
	
	//allocation aux
	aux = (int *) malloc((nPhase) * sizeof(int));
	//calcula vetor auxiliar
	for (ii=0; ii<nPhase; ii++){ 
		aux[ii] = bufferSize-bufferTau[ii];
	}	

	//allocation
	jkhP = (_Complex double *) malloc((nPhase) * sizeof(_Complex double));
	jkhQ = (_Complex double *) malloc((nPhase) * sizeof(_Complex double));
	jmhP = (_Complex double *) malloc((nPhase) * sizeof(_Complex double));
	jmhQ = (_Complex double *) malloc((nPhase) * sizeof(_Complex double));
	//initialization
	for (ii=0;ii<(nPhase);ii++){
		jkhP[ii] = 0 + 0 * I;
		jkhQ[ii] = 0 + 0 * I;
		jmhP[ii] = 0 + 0 * I;
		jmhQ[ii] = 0 + 0 * I;
	}	
	
	//allocation
	vkATP = (_Complex double *) malloc((nPhase) * sizeof(_Complex double));
	vkATPold = (_Complex double *) malloc((nPhase) * sizeof(_Complex double));
	vmATP = (_Complex double *) malloc((nPhase) * sizeof(_Complex double));
	vmATPold = (_Complex double *) malloc((nPhase) * sizeof(_Complex double));
	//initialization
	for (ii=0;ii<(nPhase);ii++){
		vkATP[ii] = 0 + 0 * I;
		vkATPold[ii] = 0 + 0 * I;
		vmATP[ii] = 0 + 0 * I;
		vmATPold[ii] = 0 + 0 * I;
	}
	//allocation
	jknP = (_Complex double **) malloc((nPhase) * sizeof(_Complex double*));
	jknQ = (_Complex double **) malloc((nPhase) * sizeof(_Complex double*));	
	jmnP = (_Complex double **) malloc((nPhase) * sizeof(_Complex double*));
	jmnQ = (_Complex double **) malloc((nPhase) * sizeof(_Complex double*));
	for (ii = 0; ii < (nPhase); ii++){
		jknP[ii] = (_Complex double *) malloc((nPoleYc) * sizeof(_Complex double));
		jknQ[ii] = (_Complex double *) malloc((nPoleYc) * sizeof(_Complex double));	
		jmnP[ii] = (_Complex double *) malloc((nPoleYc) * sizeof(_Complex double));
		jmnQ[ii] = (_Complex double *) malloc((nPoleYc) * sizeof(_Complex double));	
	}
	
	//allocation
	bkP = (_Complex double *) malloc((nPhase) * sizeof(_Complex double));
	bkQ = (_Complex double *) malloc((nPhase) * sizeof(_Complex double));
	bmP = (_Complex double *) malloc((nPhase) * sizeof(_Complex double));
	bmQ = (_Complex double *) malloc((nPhase) * sizeof(_Complex double));
	//initialization
	for (ii=0;ii<(nPhase);ii++){
		bkP[ii] = 0 + 0 * I;
		bkQ[ii] = 0 + 0 * I;
		bmP[ii] = 0 + 0 * I;
		bmQ[ii] = 0 + 0 * I;
	}
	//allocation
	bk = (_Complex double *) malloc((nPhase) * sizeof(_Complex double));
	bm = (_Complex double *) malloc((nPhase) * sizeof(_Complex double));
	bkold = (_Complex double *) malloc((nPhase) * sizeof(_Complex double));
	bmold = (_Complex double *) malloc((nPhase) * sizeof(_Complex double));
	//initialization
	for (ii=0;ii<(nPhase);ii++){
		bk[ii] = 0 + 0 * I;
		bkold[ii] = 0 + 0 * I;
		bm[ii] = 0 + 0 * I;
		bmold[ii] = 0 + 0 * I;
	}	
	
	//allocation 3D-matrix bkijP,bkijQ
	bkijP = (_Complex double ***) malloc((nPhase) * sizeof(_Complex double**));
	bkijQ = (_Complex double ***) malloc((nPhase) * sizeof(_Complex double**));
	bmijP = (_Complex double ***) malloc((nPhase) * sizeof(_Complex double**));
	bmijQ = (_Complex double ***) malloc((nPhase) * sizeof(_Complex double**));
	for (ii = 0; ii < (nPhase); ii++){
		bkijP[ii] = (_Complex double **) malloc((nPoleH) * sizeof(_Complex double*));
		bkijQ[ii] = (_Complex double **) malloc((nPoleH) * sizeof(_Complex double*));
		bmijP[ii] = (_Complex double **) malloc((nPoleH) * sizeof(_Complex double*));
		bmijQ[ii] = (_Complex double **) malloc((nPoleH) * sizeof(_Complex double*));
		for (j = 0; j < (nPoleH); j++){
			bkijP[ii][j] = (_Complex double *) malloc((nMode) * sizeof(_Complex double));
			bkijQ[ii][j] = (_Complex double *) malloc((nMode) * sizeof(_Complex double));
			bmijP[ii][j] = (_Complex double *) malloc((nMode) * sizeof(_Complex double));
			bmijQ[ii][j] = (_Complex double *) malloc((nMode) * sizeof(_Complex double));		
		}			
	}
	
	//allocation
	ikHist = (double *) malloc((nPhase) * sizeof(double));	
	imHist = (double *) malloc((nPhase) * sizeof(double));
	ikATP = (double *) malloc((nPhase) * sizeof(double));
	imATP = (double *) malloc((nPhase) * sizeof(double));
	
   //allocation
   fmBuffer = (_Complex double**) malloc((nPhase) * sizeof(_Complex double*));	
   fkBuffer = (_Complex double**) malloc((nPhase) * sizeof(_Complex double*));	
   for (ii = 0; ii < (nPhase); ii++){
	   fmBuffer[ii] = (_Complex double*) malloc((bufferSize) * sizeof(_Complex double));	
	   fkBuffer[ii] = (_Complex double*) malloc((bufferSize) * sizeof(_Complex double));	
   }	
	//initialization
	for (ii=0;ii<(nPhase);ii++){
		for (k=0;k<(bufferSize);k++){
			fmBuffer[ii][k] = 0 + 0 * I;
			fkBuffer[ii][k] = 0 + 0 * I;
		}
	}

	//allocation fmTauIntp/fmTauIntpAnt
	fmTauIntp = (_Complex double **) malloc((nPhase) * sizeof(_Complex double*));
	fkTauIntp = (_Complex double **) malloc((nPhase) * sizeof(_Complex double*));
	fmTauIntpAnt = (_Complex double **) malloc((nPhase) * sizeof(_Complex double*));
	fkTauIntpAnt = (_Complex double **) malloc((nPhase) * sizeof(_Complex double*));
	for (ii = 0; ii < (nPhase); ii++){
	   fmTauIntp[ii] = (_Complex double*) malloc((nPhase) * sizeof(_Complex double));	
	   fkTauIntp[ii] = (_Complex double*) malloc((nPhase) * sizeof(_Complex double));	
	   fmTauIntpAnt[ii] = (_Complex double*) malloc((nPhase) * sizeof(_Complex double));	
	   fkTauIntpAnt[ii] = (_Complex double*) malloc((nPhase) * sizeof(_Complex double));
	}	

	//****************************************************************************************
	
	//Constants calculation for (Yc) convolution
	for (ii=0;ii<(nPoleYc);ii++){
		pnYcvet[ii] = (2+(poleYc[ii]*deltaT))/(2-(poleYc[ii]*deltaT));	
	}
	for (k=0;k<(nPoleYc);k++){
		for (ii=0;ii<nPhase;ii++){
			for (mm=0;mm<nPhase;mm++){				
				rnYc[ii][mm][k] = resYc[ii][mm][k]*(deltaT*(1/(2-(poleYc[k]*deltaT)))); 
				
			}
		}
	}
	for (ii=0;ii<nPhase;ii++){
		for (j=0;j<nPhase;j++){
			sumrnYc[ii][j] = 0 + 0 * I;
		}
	}
	for (ii=0;ii<nPhase;ii++){
		for (j=0;j<nPhase;j++){
			for (k=0;k<nPoleYc;k++){
				sumrnYc[ii][j] += rnYc[ii][j][k];
			}
		}
	}
	
	//****************************************************************************************
	
	//Constants calculation for (A) convolution
	for (ii=0;ii<(nPoleH);ii++){
		pnAvet[ii] = (2+(poleH[ii]*deltaT))/(2-(poleH[ii]*deltaT));
	}
	for (j=0;j<(nMode);j++){
		for (k=0;k<(nPoleH);k++){
			for (ii=0;ii<(nPhase);ii++){
				for (mm=0;mm<(nPhase);mm++){
					rnA[ii][mm][k][j] = resH[ii][mm][k][j]*(deltaT*(1/(2-(poleH[k]*deltaT)))); 
				}
			}
		}	
	}	
	for (k=0;k<(nMode);k++){
		for (ii=0;ii<(nPhase);ii++){
			for (j=0;j<(nPhase);j++){
				sumrnA[ii][j][k] = 0 + 0 * I;
			}
		}
	}
	for (j=0;j<(nMode);j++){
		for (ii=0;ii<(nPhase);ii++){
			for (mm=0;mm<(nPhase);mm++){
				for (k=0;k<(nPoleH);k++){
					sumrnA[ii][mm][j] += rnA[ii][mm][k][j]; 
				}
			}
		}
	}
	
	//****************************************************************************************
	
	//Gulm calculation
	for (ii=0;ii<nPhase;ii++){
		for (j=0;j<nPhase;j++){
			Gulm[ii][j]=sumrnYc[ii][j]+resid0Yc[ii][j];
		}
	}	
	
	//****************************************************************************************
	
	//Import voltages and currents from ATP
	for (ii=0; ii<nPhase; ii++){ 
	vkATP[ii] = 0;
	}
	for (ii=nPhase; ii<2*nPhase; ii++){ 
	ikATP[ii-nPhase] = 0;
	}
	for (ii=2*nPhase; ii<3*nPhase; ii++){ 
	vmATP[ii-2*nPhase] = 0;
	}
	for (ii=3*nPhase; ii<4*nPhase; ii++){ 
	imATP[ii-3*nPhase] = 0;
	}	
	
	//Export ikHist,imHist to ATP	
	for (ii=0; ii<nPhase; ii++){
	xout_ar[ii] = 0;
	}
	for (ii=nPhase; ii<2*nPhase; ii++){
	xout_ar[ii] = 0;
	}

	return;
}
