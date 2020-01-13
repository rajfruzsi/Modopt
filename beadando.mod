/*
A feladat, hogy egy edzőlétesítményben megtartott edzésekkel az összes vendég úgy tudjon edzeni, hogy hét végére a legtöbb kalóriát égesse el.
Minden Vendégnek vannak preferált napjai, amikor tud edzeni menni, illetve preferált kalóriaszám, amit minimum el akar égetni az adott héten, és egy maximum is,
hogy ne hajszolja túl magát. 
Minden Edzés ugyanakkor fix összegbe kerül, így a Vendégeknek bele kell férnie a saját heti keretükbe. Egy Edzésen előre megadott létszám vehet részt az adott napon, és az edzések a létesítmény egyes termeiben zajlanak le. Természetesen egy edzés nem történhet egyszerre 2 teremben, és, ha aznap egy ember sem venne részt az edzésen (az egyéni preferenciák stb.) miatt, akkor ne is legyen terembe beosztva edzés.
Az edzőlétesítményben több terem is található, amik megadott kapacitással rendelkeznek, így abba bele kell férnie az edzés résztvevőinek, ha nem, akkor másik terembe kerül át az edzés. A termeknek van egy foglaltsági tulajdonsága is, így amikor az adott nap valamiért a terem nem elérhető, ott edzést sem lehet tartani.
Minden Vendég számára van olyan másik Vendég akit kevésbé szívlel, így azokkal nem szeretne együtt edzeni. A Vendégeknél oda kell arra is figyelni, hogy egy héten egy testrészre csakis egyszer edzhetnek.
A modell célja tehát egy olyan beosztás elkészítése, ami megfelel az összes fent leírtnak.
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

#Vendégekkel kapcsolatos korlátozások
#minden edzésen max a megengedett létszám vehet részt
s.t. MaxLetszam{e in Edzesek, n in Napok: maxfo[e,n]!=0}:
	sum{v in Vendegek}mit[v,e,n]<=maxfo[e,n];
#preferalt napon menjen edzeni
s.t. PreferaltNap{v in Vendegek, e in Edzesek, n in Napok:preferaltIdopont[v,n]=0}:
	mit[v,e,n]=0;

#ne eddzen azzal akit nem szeret
s.t. NeEddzenHaNemSzereti{e in Edzesek, n in Napok,v in Vendegek, v2 in Vendegek:baratok[v,v2]=0}:
	mit[v,e,n]+mit[v2,e,n]<=1;

#csak akkor mehet edzeni amikor van edzés, vagyis amikor a létszám több mint 0
s.t. csakAmikorVanEdzes{v in Vendegek, e in Edzesek, n in Napok: maxfo[e,n]=0}:
	mit[v,e,n]=0;

#de ne legyentöbb mint a maxkaloria a héten
s.t. NehajszoljaTulmagat{v in Vendegek}:
	sum{n in Napok, e in Edzesek}mit[v,e,n]*kaloria[e]<=maxkaloria[v];

#férjen bele a keretébe
s.t. MaxPenz{v in Vendegek}:
	sum{n in Napok, e in Edzesek}mit[v,e,n]*dij[e]<=maxPenz[v];

#egynapcsak egy edzés
s.t. egyNapMaxEgy{n in Napok, v in Vendegek}:
	sum{e in Edzesek}mit[v,e,n]<=1;

#egy héten egy testrészt csak egyszer lehet
s.t. MaxegyTestresz{t in Testresz, v in Vendegek}:
	sum{n in Napok,e in Edzesek}mit[v,e,n]*testresz[e,t]<=1;
#úgymenjen edzeni hogy meglegyen a preferált kalória
s.t. MenjenedzeniEleget{v in Vendegek}:
	sum{n in Napok, e in Edzesek}mit[v,e,n]*kaloria[e]>=preferaltKaloria[v];

#Termekkel kapcsolatos korlátozások
#egy nap egy edzés csak egyszer
s.t. EgyNapEgyEdzes{n in Napok, e in Edzesek}:
	sum{t in Terem}hol[e,t,n]<=1;

#ha adott napon nincs edzés vagy nem szabad a terem akkor nem is lehet ott edzés
s.t. HaNemszabadVagyNincsedzesNemkellterem{n in Napok, t in Terem, e in Edzesek:maxfo[e,n]=0 || szabad[t,n]=0}:
	hol[e,t,n]=0;

#ha van edzés akkor teremben legyen
s.t. TeremFoglalas{v in Vendegek,e in Edzesek, n in Napok}:
	mit[v,e,n]<=sum{t in Terem}hol[e,t,n];

#ha egy ember se menne arra az adott edzésre, akkor ne is legyen annak terem foglalva
s.t. HaNincsEmberEdzesreAkkorNelegyenTerem{ t in Terem, e in Edzesek, n in Napok}:
	hol[e,t,n]<=sum{v in Vendegek}mit[v,e,n];
	

#egy nap egy teremben csak egy edzés lehetséges
s.t. EgyNapEgyTerembenEgyEdzes{n in Napok, t in Terem}:
	sum{e in Edzesek}hol[e,t,n]<=1;


maximize Bevetel:
	sum{t in Terem,n in Napok,e in Edzesek}(hol[e,t,n]*penz[t]);

solve;

printf "Mikor mire megy: \n";

		for{n in Napok,v in Vendegek, e in Edzesek,t in Terem:mit[v,e,n]=1 && hol[e,t,n]=1}
				printf "%s : %s ezt edzette: %s a %s-ben \n\n",n,v,e,t;
				printf "\n";
				

				
end;
