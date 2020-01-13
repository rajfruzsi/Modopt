/*
A feladat, hogy egy edz�l�tes�tm�nyben megtartott edz�sekkel az �sszes vend�g �gy tudjon edzeni, hogy h�t v�g�re a legt�bb kal�ri�t �gesse el.
Minden Vend�gnek vannak prefer�lt napjai, amikor tud edzeni menni, illetve prefer�lt kal�riasz�m, amit minimum el akar �getni az adott h�ten, �s egy maximum is,
hogy ne hajszolja t�l mag�t. 
Minden Edz�s ugyanakkor fix �sszegbe ker�l, �gy a Vend�geknek bele kell f�rnie a saj�t heti keret�kbe. Egy Edz�sen el�re megadott l�tsz�m vehet r�szt az adott napon, �s az edz�sek a l�tes�tm�ny egyes termeiben zajlanak le. Term�szetesen egy edz�s nem t�rt�nhet egyszerre 2 teremben, �s, ha aznap egy ember sem venne r�szt az edz�sen (az egy�ni preferenci�k stb.) miatt, akkor ne is legyen terembe beosztva edz�s.
Az edz�l�tes�tm�nyben t�bb terem is tal�lhat�, amik megadott kapacit�ssal rendelkeznek, �gy abba bele kell f�rnie az edz�s r�sztvev�inek, ha nem, akkor m�sik terembe ker�l �t az edz�s. A termeknek van egy foglalts�gi tulajdons�ga is, �gy amikor az adott nap valami�rt a terem nem el�rhet�, ott edz�st sem lehet tartani.
Minden Vend�g sz�m�ra van olyan m�sik Vend�g akit kev�sb� sz�vlel, �gy azokkal nem szeretne egy�tt edzeni. A Vend�gekn�l oda kell arra is figyelni, hogy egy h�ten egy testr�szre csakis egyszer edzhetnek.
A modell c�lja teh�t egy olyan beoszt�s elk�sz�t�se, ami megfelel az �sszes fent le�rtnak.
*/


set Napok;
set Edzesek;
set Testresz;
set Terem;

param kapacitas{Terem};
param penz{Terem};
param szabad{Terem, Napok};

param dij{Edzesek};
param kaloria{Edzesek};
param testresz{Edzesek,Testresz};
param maxfo{Edzesek, Napok};


set Vendegek;
param preferaltIdopont{Vendegek,Napok};
param maxPenz{Vendegek};
param preferaltKaloria{Vendegek};
param maxkaloria{Vendegek};
param baratok{Vendegek, Vendegek};

var mit{Vendegek, Edzesek,Napok} binary;
var hol{Edzesek, Terem, Napok} binary;

#Vend�gekkel kapcsolatos korl�toz�sok
#minden edz�sen max a megengedett l�tsz�m vehet r�szt
s.t. MaxLetszam{e in Edzesek, n in Napok: maxfo[e,n]!=0}:
	sum{v in Vendegek}mit[v,e,n]<=maxfo[e,n];
#preferalt napon menjen edzeni
s.t. PreferaltNap{v in Vendegek, e in Edzesek, n in Napok:preferaltIdopont[v,n]=0}:
	mit[v,e,n]=0;

#ne eddzen azzal akit nem szeret
s.t. NeEddzenHaNemSzereti{e in Edzesek, n in Napok,v in Vendegek, v2 in Vendegek:baratok[v,v2]=0}:
	mit[v,e,n]+mit[v2,e,n]<=1;

#csak akkor mehet edzeni amikor van edz�s, vagyis amikor a l�tsz�m t�bb mint 0
s.t. csakAmikorVanEdzes{v in Vendegek, e in Edzesek, n in Napok: maxfo[e,n]=0}:
	mit[v,e,n]=0;

#de ne legyent�bb mint a maxkaloria a h�ten
s.t. NehajszoljaTulmagat{v in Vendegek}:
	sum{n in Napok, e in Edzesek}mit[v,e,n]*kaloria[e]<=maxkaloria[v];

#f�rjen bele a keret�be
s.t. MaxPenz{v in Vendegek}:
	sum{n in Napok, e in Edzesek}mit[v,e,n]*dij[e]<=maxPenz[v];

#egynapcsak egy edz�s
s.t. egyNapMaxEgy{n in Napok, v in Vendegek}:
	sum{e in Edzesek}mit[v,e,n]<=1;

#egy h�ten egy testr�szt csak egyszer lehet
s.t. MaxegyTestresz{t in Testresz, v in Vendegek}:
	sum{n in Napok,e in Edzesek}mit[v,e,n]*testresz[e,t]<=1;
#�gymenjen edzeni hogy meglegyen a prefer�lt kal�ria
s.t. MenjenedzeniEleget{v in Vendegek}:
	sum{n in Napok, e in Edzesek}mit[v,e,n]*kaloria[e]>=preferaltKaloria[v];

#Termekkel kapcsolatos korl�toz�sok
#egy nap egy edz�s csak egyszer
s.t. EgyNapEgyEdzes{n in Napok, e in Edzesek}:
	sum{t in Terem}hol[e,t,n]<=1;

#ha adott napon nincs edz�s vagy nem szabad a terem akkor nem is lehet ott edz�s
s.t. HaNemszabadVagyNincsedzesNemkellterem{n in Napok, t in Terem, e in Edzesek:maxfo[e,n]=0 || szabad[t,n]=0}:
	hol[e,t,n]=0;

#ha van edz�s akkor teremben legyen
s.t. TeremFoglalas{v in Vendegek,e in Edzesek, n in Napok}:
	mit[v,e,n]<=sum{t in Terem}hol[e,t,n];

#ha egy ember se menne arra az adott edz�sre, akkor ne is legyen annak terem foglalva
s.t. HaNincsEmberEdzesreAkkorNelegyenTerem{ t in Terem, e in Edzesek, n in Napok}:
	hol[e,t,n]<=sum{v in Vendegek}mit[v,e,n];
	

#egy nap egy teremben csak egy edz�s lehets�ges
s.t. EgyNapEgyTerembenEgyEdzes{n in Napok, t in Terem}:
	sum{e in Edzesek}hol[e,t,n]<=1;

	

#ha 
maximize Bevetel:
	sum{t in Terem,n in Napok,e in Edzesek}(hol[e,t,n]*penz[t]);

solve;

printf "Mikor mire megy: \n";

		for{n in Napok,v in Vendegek, e in Edzesek,t in Terem:mit[v,e,n]=1 && hol[e,t,n]=1}
				printf "%s : %s ezt edzette: %s a %s-ben \n\n",n,v,e,t;
				printf "\n";
				
				


printf "Mikor mi hol: \n";
for{n in Napok}
		for{e in Edzesek, t in Terem: hol[e,t,n]=1}
				printf "%s -n %s edz�s %s-ben  \n\n",n,e,t;
				printf "\n";
				

printf "Mikor mire megyjuihu: \n";

		for{n in Napok,v in Vendegek, e in Edzesek:mit[v,e,n]=1 }
				printf "%s -n %s ezt edzette: %s  \n\n",n,v,e;
				printf "\n";
				
				
end;
