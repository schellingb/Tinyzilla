/*
  Tinyzilla
  Copyright (C) 2024 Bernhard Schelling

  This software is provided 'as-is', without any express or implied
  warranty.  In no event will the authors be held liable for any damages
  arising from the use of this software.

  Permission is granted to anyone to use this software for any purpose,
  including commercial applications, and to alter it and redistribute it
  freely, subject to the following restrictions:

  1. The origin of this software must not be misrepresented; you must not
     claim that you wrote the original software. If you use this software
     in a product, an acknowledgment in the product documentation would be
     appreciated but is not required.
  2. Altered source versions must be plainly marked as such, and must not be
     misrepresented as being the original software.
  3. This notice may not be removed or altered from any source distribution.
*/

#include <ZL_Application.h>
#include <ZL_Display.h>
#include <ZL_Surface.h>
#include <ZL_Signal.h>
#include <ZL_Audio.h>
#include <ZL_Font.h>
#include <ZL_Scene.h>
#include <ZL_Input.h>
#include <ZL_SynthImc.h>

#include <iostream>
#include <map>
#include <vector>
#include <list>
#include <algorithm>
using namespace std;

static ZL_Font fntMain, fntBig;
static ZL_Surface srfGrass, srfWall, srfPlayer, srfTiny, srfEgg, srfHive, srfBug;
static ZL_Sound sndGrow, sndTinyHit, sndBugHit, sndPursue, sndTinyDie, sndBugDie;
static ZL_SynthImcTrack imcMusic;

static void DrawTextBordered(const ZL_Vector& p, const char* txt, float scale = 1, const ZL_Color& colfill = ZLWHITE, const ZL_Color& colborder = ZLBLACK, int border = 2, ZL_Origin::Type origin = ZL_Origin::Center)
{
	for (int i = 0; i < 9; i++) if (i != 4) fntMain.Draw(p.x+(border*((i%3)-1)), p.y+8+(border*((i/3)-1)), txt, scale, scale, colborder, origin);
	fntMain.Draw(p.x  , p.y+8  , txt, scale, scale, colfill, origin);
}

enum { GENSIZE = 17, GENW = GENSIZE, GENH = GENSIZE };
enum { MAXMAPSIZE = (GENSIZE - 2) * 2 + 1, MAPW = MAXMAPSIZE, MAPH = MAXMAPSIZE };
static char Map[MAXMAPSIZE*MAXMAPSIZE+1];
enum eTILE : char { TILE_EMPTY = ' ', TILE_WALL = '#' };
#define TILEINDEX_FROM_POS(x, y) ((int)(y)*MAPW+(int)(x))
#define POS_FROM_TILEINDEX(idx) ZLV(.5f+(idx%MAPW), .5f+(idx/MAPW))

struct SpiralRange
{
	inline SpiralRange(int idxstart) : x(idxstart%MAPW), y(idxstart/MAPW) {}
	inline SpiralRange& begin() { return *this; }
	inline SpiralRange& end() { return *this; }
	inline SpiralRange operator++()
	{
		do
		{
			x -= tilex, y -= tiley;
			if ((tilex == tiley) || ((tilex < 0) && (tilex == -tiley)) || ((tilex > 0) && (tilex == 1-tiley))) { int t = deltax; deltax = -deltay; deltay = t; } // Reached a corner, turn left
			x += (tilex += deltax), y += (tiley += deltay);
		} while (x < 1 || x >= MAPW-1 || y < 1 || y >= MAPH-1);
		return *this; 
	}
	inline bool operator!=(const SpiralRange & other) const { return true; }
	inline int operator*() const { return x + y * MAPW; }
	int x, y, tilex = 0, tiley = 0, deltax = 0, deltay = -1;
};

enum eType : unsigned char
{
	TYPE_NONE = 0,
	TYPE_PLAYER = 1,
	TYPE_TINY = 2,
	TYPE_EGG = 4,
	TYPE_NEWEGG = 8,
	TYPE_HIVE = 16,
	TYPE_BUG = 32,
	TYPEMASK_MOVE = (TYPE_TINY | TYPE_BUG),
	TYPEMASK_COLLIDE = (TYPE_PLAYER | TYPE_TINY | TYPE_BUG),
	TYPEMASK_PURSUE = (TYPE_PLAYER | TYPE_BUG | TYPE_EGG | TYPE_NEWEGG),
};

struct sCreature
{
	eType Type;
	unsigned char Tick;
	bool LastCollidedCreature;
	ZL_Vector Pos, UIPos;
	float LookAngle, Radius, MoveDist;
	ZL_Color Color;
	sCreature* AttackTarget;
	int Health, MaxHealth, MoveTarget, MoveNext;

	sCreature() : Type(TYPE_NONE), Tick(0), LastCollidedCreature(false), Pos(ZLV(0,0)), LookAngle(0), Radius(0.5f), MoveDist(0), AttackTarget(NULL), Health(100), MaxHealth(100), MoveTarget(-1), MoveNext(-1) {}
	sCreature(eType t, ZL_Vector p) : sCreature() { Setup(t, p); }

	void Setup(eType t, ZL_Vector p)
	{
		int px = ZL_Math::Clamp((int)sfloor(p.x), 1, MAPW-1), py = ZL_Math::Clamp((int)sfloor(p.y), 1, MAPH-1);
		int idxp = (px + py * MAPW);
		if (Map[idxp] == TILE_WALL) { for (int i : SpiralRange(idxp)) { if (Map[i] == TILE_EMPTY) { idxp = i; break; } } }

		Radius = ((t == TYPE_PLAYER || t == TYPE_BUG) ? 0.4f : 0.2f);
		if (Type == TYPE_NONE) Color = ZLHSV(RAND_FACTOR, .5, 1);
		Health = MaxHealth = (t == TYPE_PLAYER ? 10 : (t == TYPE_EGG ? 5 : (t == TYPE_TINY ? 20 : 100)));
		Type = t;
		Pos = p;
	}
};

static std::vector<sCreature> creatures;
static ZL_Vector fixedPursuePos;
static sCreature* fixedPursueCreature;
static int Stage, BugSpawnRemain, BugSpawnTick, BugSpawnTime, BugAttackDamage;
static float grassSlant = -0.1f;
static ZL_Color wallColor;
static ticks_t stageStartTicks;

void UpdatePos(sCreature& c, ZL_Vector Dir, float Speed)
{
	ZL_Vector Pos = c.Pos;
	Pos = Pos + Dir * Speed;
	const float MAPMINX = 0 + KINDA_SMALL_NUMBER, MAPMAXX = MAPW - KINDA_SMALL_NUMBER, MAPMINY = 0 + KINDA_SMALL_NUMBER, MAPMAXY = MAPH - KINDA_SMALL_NUMBER;
	if (Pos.x < MAPMINX) Pos.x = MAPMINX;
	if (Pos.x > MAPMAXX) Pos.x = MAPMAXX;
	if (Pos.y < MAPMINY) Pos.y = MAPMINY;
	if (Pos.y > MAPMAXY) Pos.y = MAPMAXY;

	c.LookAngle = Dir.GetAngle();

	struct sCol { ZL_Vector pos1, pos2, dir; int ismap; float dist; };
	static std::vector<sCol> cols;
	cols.clear();

	int xfrom = ZL_Math::Clamp((int)sfloor(Pos.x - 1.0f), 0, (MAPW-1)), xto = ZL_Math::Clamp((int)sfloor(Pos.x + 1.0f), 0, (MAPW-1));
	int yfrom = ZL_Math::Clamp((int)sfloor(Pos.y - 1.0f), 0, (MAPH-1)), yto = ZL_Math::Clamp((int)sfloor(Pos.y + 1.0f), 0, (MAPH-1));
	for (int y = yfrom ; y <= yto; y++)
		for (int x = xfrom ; x <= xto; x++)
		{
			int ti = (x + y * MAPW);
			if (Map[ti] == TILE_EMPTY) continue;
			if (Pos.x > s(x + 1)) cols.push_back({ZLV(x+1.0f, y-0.0f), ZLV(x+1.0f, y+1.0f), ZLV( 1,0), 1});
			if (Pos.x < s(x    )) cols.push_back({ZLV(x+0.0f, y-0.0f), ZLV(x+0.0f, y+1.0f), ZLV(-1,0), 1});
			if (Pos.y > s(y + 1)) cols.push_back({ZLV(x-0.0f, y+1.0f), ZLV(x+1.0f, y+1.0f), ZLV(0, 1), 1});
			if (Pos.y < s(y    )) cols.push_back({ZLV(x-0.0f, y+0.0f), ZLV(x+1.0f, y+0.0f), ZLV(0,-1), 1});
		}

	eType ignoremask = (eType)(~TYPEMASK_COLLIDE | (c.Type == TYPE_PLAYER ? TYPE_TINY : (c.Type == TYPE_TINY ? TYPE_PLAYER : TYPE_NONE)));
	for (sCreature& e : creatures)
	{
		if (&e == &c || (e.Type & ignoremask) || !e.Health) continue;
		ZL_Vector d = Pos - e.Pos;
		float distSq = d.GetLengthSq();
		if (distSq > ZL_Math::Square(e.Radius + c.Radius + .25f)) continue;
		if (distSq < 0.01f) continue; // too close to fix
		d.Div(ssqrt(distSq));
		ZL_Vector pt = e.Pos + d * e.Radius;
		cols.push_back({pt, pt, d, 0});
	}

	if (cols.empty()) { c.MoveDist += Pos.GetDistance(c.Pos); c.Pos = Pos; c.LastCollidedCreature = false; return; };
	sCol *colBegin = &cols[0], *colEnd = colBegin + cols.size();
	for (sCol* col = colBegin; col != colEnd; col++) col->dist = Pos.GetDistanceSq(col->ismap ? ((col->pos1+col->pos2)*0.5f) : col->pos1);
	sort(colBegin, colEnd, [](const sCol& a, const sCol& b) { return (a.ismap < b.ismap || (a.ismap == b.ismap && a.dist < b.dist)); });

	c.LastCollidedCreature = false;
	for (int it = 0; ; it++)
	{
		bool collided = false;
		for (sCol* col = colBegin; col != colEnd; col++)
		{
			col->dist = (Pos - col->pos1) | col->dir;
			if (col->dist > c.Radius) continue;

			if (!(col->ismap ? ZL_Math::LineCircleCollision(col->pos1, col->pos2, Pos, c.Radius) : col->pos1.Near(Pos, c.Radius))) continue;
			Pos += col->dir * (c.Radius - col->dist + 0.001f);
			collided = true;
			if (!col->ismap) c.LastCollidedCreature = true;
		}
		if (!collided) { c.MoveDist += Pos.GetDistance(c.Pos); c.Pos = Pos; return; }
		if (it > (int)cols.size()) return; // give up
	}
}

ZL_Vector AStarUpdate(sCreature& c, ZL_Vector to)
{
	int Frontier[MAXMAPSIZE*MAXMAPSIZE], Path[MAXMAPSIZE*MAXMAPSIZE];
	bool Visited[MAXMAPSIZE*MAXMAPSIZE];
	memset(&Visited, 0, sizeof(Visited));
	const ZL_Vector from = c.Pos;
	int ifromx = ZL_Math::Clamp((int)sfloor(from.x), 0, MAPW-1), ifromy = ZL_Math::Clamp((int)sfloor(from.y), 0, MAPH-1);
	int itox = ZL_Math::Clamp((int)sfloor(to.x), 0, MAPW-1), itoy = ZL_Math::Clamp((int)sfloor(to.y), 0, MAPH-1);

	int idxFrom = (ifromx + ifromy * MAPW);
	int idxTo   = (itox   + itoy   * MAPW);
	if (idxTo == idxFrom) return to;
	if (idxTo == c.MoveTarget)
	{
		if (idxFrom != c.MoveNext) return POS_FROM_TILEINDEX(c.MoveNext);
		ZL_Vector vFrom = POS_FROM_TILEINDEX(idxFrom);
		if (!c.LastCollidedCreature && from.Far(vFrom, 0.1f)) return vFrom; // make sure we reached the center of the tile (unless colliding with other creatures)
	}

	if (Map[idxTo]   == TILE_WALL) { for (int i : SpiralRange(idxTo  )) { if (Map[i] == TILE_EMPTY) { idxTo   = i; break; } } }
	if (Map[idxFrom] == TILE_WALL) { for (int i : SpiralRange(idxFrom)) { if (Map[i] == TILE_EMPTY) { idxFrom = i; break; } } }
	if (idxTo == idxFrom) return to;

	int FrontierDone = 0, FrontierCount = 0;
	Frontier[FrontierCount++] = idxFrom;
	Visited[idxFrom] = true;
	static int NeighborOfs[] = { 1, -1, MAPW, -MAPW, MAPW+1, MAPW-1, -MAPW+1, -MAPW-1 };
	static int CheckOfs1[]   = { 0,  0,    0,     0, MAPW  , MAPW  , -MAPW  , -MAPW   };
	static int CheckOfs2[]   = { 0,  0,    0,     0,      1,     -1,       1,      -1 };
	while (FrontierDone != FrontierCount)
	{
		int idx = Frontier[FrontierDone++];
		for (int dir = 0; dir != 8; dir++)
		{
			int idxNeighbor = idx + NeighborOfs[dir];
			if (Visited[idxNeighbor]) continue;
			int xDiff = (idx%MAPW) - (idxNeighbor%MAPW);
			if (xDiff > 1 || xDiff < -1) continue;

			Visited[idxNeighbor] = true;
			if (Map[idxNeighbor] != TILE_EMPTY) continue;
			if (CheckOfs1[dir] && (Map[idx + CheckOfs1[dir]] != TILE_EMPTY || Map[idx + CheckOfs2[dir]] != TILE_EMPTY)) { Visited[idxNeighbor] = false; continue; }

			Frontier[FrontierCount++] = idxNeighbor;
			if (idxNeighbor == idxTo)
			{
				int Steps = 0;
				for (int idx1 = idxNeighbor, idx2 = idx, idx3; idx1 != idxFrom; idx1 = idx2, idx2 = idx3, Steps++)
				{
					ZL_ASSERT(idx2 >= 0 && idx2 < MAPW*MAPH);
					idx3 = Path[idx2];
					Path[idx2] = idx1;
				}
				int idxTarget = Path[idxFrom], diff = idxTarget - idxFrom;
				ZL_Vector vTarget = POS_FROM_TILEINDEX(idxTarget);
				if (idxTarget != idxTo && (Path[idxTarget] - idxTarget) == diff)
				{
					// when heading straight, we can target a tile multiple steps ahead
					ZL_Vector vFrom = POS_FROM_TILEINDEX(idxFrom);
					float cp = (vTarget - from).Norm() | (vTarget - vFrom).NormUnsafe();
					if (cp > 0.99f)
					{
						do { idxTarget = Path[idxTarget]; } while (idxTarget != idxTo && (Path[idxTarget] - idxTarget) == diff);
						vTarget = POS_FROM_TILEINDEX(idxTarget);
					}
				}
				c.MoveTarget = idxTo;
				c.MoveNext = idxTarget;
				return vTarget;
			}
			Path[idxNeighbor] = idx;
		}
	}
	return to; //no path
}

static void InitStage(int fixstage)
{
	char tmp[GENSIZE*GENSIZE+1];
	tmp[GENW*GENH] = '\0';
	memset(tmp, TILE_WALL, GENW*GENH);

	int playerX = RAND_INT_RANGE(2, GENW-3);
	int playerY = RAND_INT_RANGE(2, GENH-3);
	tmp[playerX*GENW+playerY] = TILE_EMPTY;
	
	for (char empty = 0; empty < 4 - MIN(4/2, 2); empty++)
	{
		int currentx = GENW/2|1, currenty = GENH/2|1;
		for (int y = currenty - 2; y <= currenty + 2; y++)
			for (int x = currentx - 2; x <= currentx + 2; x++)
				tmp[y*GENW+x] = empty;
 
		REGENERATE:
		for (int i = 0; i != 100; i++)
		{
			int oldx = currentx, oldy = currenty;
			switch (RAND_INT_MAX(3))
			{
				case 0: if (currentx < GENW-2) currentx += 2; break;
				case 1: if (currenty < GENH-2) currenty += 2; break;
				case 2: if (currentx >      2) currentx -= 2; break;
				case 3: if (currenty >      2) currenty -= 2; break;
			}
			if (tmp[currenty*GENW+currentx] == empty) continue;
			tmp[currenty*GENW+currentx] = empty;
			tmp[((currenty + oldy) / 2)*GENW+((currentx + oldx) / 2)] = empty;
		}
 
		//check if all cells are visited
		for (int y = 1; y != GENH; y += 2)
			for (int x = 1; x != GENW; x += 2)
				if (tmp[y*GENW+x] > TILE_EMPTY) goto REGENERATE;
	}

	for (char& c : tmp) if (c < TILE_EMPTY) c = TILE_EMPTY;

	// Make sure the lower left is free
	for (int y = 0; y != 4; y++)
		for (int x = 0; x != 4; x++)
			tmp[y*GENW+x] = TILE_EMPTY;

	// Translate to higher resolution map
	memset(Map, TILE_EMPTY, MAPW*MAPH);
	for (int y = 1; y != GENH-1; y++)
		for (int x = 1; x != GENW-1; x++)
		{
			char *ptmp = &tmp[y*GENW+x];
			if (ptmp[0] == TILE_EMPTY) continue;

			char *pmap = &Map[((y-1)*2+1)*MAPW + (x-1)*2+1];
			bool use = false;
			if (ptmp[    1] == TILE_WALL) { ZL_ASSERT(&pmap[    1] >= Map && &pmap[    1] < Map+COUNT_OF(Map)); pmap[    1] = TILE_WALL; use = true; }
			if (ptmp[   -1] == TILE_WALL) { ZL_ASSERT(&pmap[   -1] >= Map && &pmap[   -1] < Map+COUNT_OF(Map)); pmap[   -1] = TILE_WALL; use = true; }
			if (ptmp[ GENW] == TILE_WALL) { ZL_ASSERT(&pmap[ MAPW] >= Map && &pmap[ MAPW] < Map+COUNT_OF(Map)); pmap[ MAPW] = TILE_WALL; use = true; }
			if (ptmp[-GENW] == TILE_WALL) { ZL_ASSERT(&pmap[-MAPW] >= Map && &pmap[-MAPW] < Map+COUNT_OF(Map)); pmap[-MAPW] = TILE_WALL; use = true; }
			if (use) pmap[0] = TILE_WALL;
		}

	int nTinies = 1, nFreeEggs, nHoles;

	Stage = (fixstage ? fixstage : (Stage ? Stage + 1 : 1));

	switch (Stage)
	{
		case 1:
			nHoles = 3;
			nFreeEggs = 5;
			BugSpawnRemain = 3;
			BugSpawnTick = -100;
			BugSpawnTime = 500;
			BugAttackDamage = 1;
			wallColor = ZLWHITE;
			grassSlant = -0.1f;
			break;

		case 2:
			nHoles = 3;
			nFreeEggs = 5;
			BugSpawnRemain = 5;
			BugSpawnTick = -100;
			BugSpawnTime = 400;
			BugAttackDamage = 2;
			wallColor = ZL_Color::Brown;
			grassSlant = 0.1f;
			break;

		case 3:
			nHoles = 3;
			nFreeEggs = 5;
			BugSpawnRemain = 10;
			BugSpawnTick = -100;
			BugSpawnTime = 300;
			BugAttackDamage = 3;
			wallColor = ZL_Color::Red;
			grassSlant = -0.3f;
			break;
	}

	if (Stage == 1)
	{
		creatures.resize(0);
	}
	else
	{
		nTinies = 0;
		for (size_t i = creatures.size(); i--;)
			if (!(creatures[i].Type & (TYPE_PLAYER | TYPE_TINY)))
				creatures.erase(creatures.begin() + i);
			else if (creatures[i].Type == TYPE_PLAYER)
				creatures[i].Pos = ZLV(2.5f, 2.5f);
			else
			{
				creatures[i].AttackTarget = NULL;
				creatures[i].Pos = ZLV(2.5f, 2.5f) + ZL_Vector::FromAngle(nTinies * .6f) * (.4f + nTinies * .05f);
				nTinies++;
			}

	}

	int nSpawnEggs = BugSpawnRemain * 3; // 3 eggs per bug kill
	creatures.reserve(1 + nTinies + nFreeEggs + nHoles + BugSpawnRemain + nSpawnEggs);
	if (Stage == 1)
	{
		creatures.emplace_back(TYPE_PLAYER, ZLV(2.5f, 2.5f));
		creatures.emplace_back(TYPE_TINY, ZLV(3.5f, 2.5f)); // initial tiny
	}

	for (int i = 0; i != nFreeEggs; i++)
		creatures.emplace_back(TYPE_EGG, ZLV(.5f + 2.0f*RAND_INT_MAX(MAPW/2-1), .5f + 2.0f*RAND_INT_MAX(MAPH/2-1)));

	if (nHoles > 0) creatures.emplace_back(TYPE_HIVE, ZLV(MAPW - 1.0f, MAPH - 1.0f));
	if (nHoles > 1) creatures.emplace_back(TYPE_HIVE, ZLV(MAPW - 1.0f, 1.0f));
	if (nHoles > 2) creatures.emplace_back(TYPE_HIVE, ZLV(       1.0f, MAPH - 1.0f));

	ZL_ASSERT(creatures[0].Type == TYPE_PLAYER);
	fixedPursueCreature = &creatures[0];
	stageStartTicks = ZLTICKS;
}

static void Update()
{
	static bool paused, titleDone;
	static float titleTime;
	if (!titleDone)
	{
		titleTime += ZLELAPSED;
		float a = 1 - ZL_Math::Clamp01(titleTime * .8f);
		ZL_Display::FillRect(0, 0, ZLWIDTH, ZLHEIGHT, ZLRGBA(0, .1, 0, .7f+a*.3f));
		ZL_Display::PushMatrix();
		ZL_Display::Translate(ZL_Display::Center());
		ZL_Display::Rotate(ZLTICKS*.001f);
		for (int i = 0; i < 100; i++)
		{
			float x = (5000 - ((ZLTICKS + i * 50) % 5000)) / 5000.f;
			ZL_Display::Rotate(.3f + (ZLTICKS * .00001f));
			srfTiny.Draw(ZLV(x * ZLHALFW*1.7f, 0), x * 20.f, x * 4.f, x * 4.f, ZLHSVA(i/100.0f, .5, 1, .3));
		}
		ZL_Display::PopMatrix();
		ZL_Display::PushMatrix();
		ZL_Display::Translate(ZLV(ZLHALFW, ZLHALFH+100));
		for (int i = 0; i < 10; i++)
		{
			ZL_Display::PushMatrix();
			ZL_Display::Rotate(RAND_RANGE(-.05f, .05f));
			fntBig.Draw(RAND_RANGE(-10,10), RAND_RANGE(-10,10), "TINYZILLA", 1.35f, 1.35f, ZLLUMA(0, .3f), ZL_Origin::Center);
			ZL_Display::PopMatrix();
		}
		ZL_Display::PopMatrix();
		fntBig.Draw(ZLV(ZLHALFW, ZLHALFH+100), "TINYZILLA", 1.25f, 1.25f, ZLHSV(smod(ZLTICKS*.001f,1),.2f,1), ZL_Origin::Center);

		DrawTextBordered(ZLV(ZLHALFW, ZLHALFH-40), "Hatch Tinies from eggs and eliminate the bug threat!");
		DrawTextBordered(ZLV(ZLHALFW, ZLHALFH-100), "Hold Right-Click to Move (or WASD)");
		DrawTextBordered(ZLV(ZLHALFW, ZLHALFH-140), "Press Left-Click to Focus Tinies");
		DrawTextBordered(ZLV(ZLHALFW, ZLHALFH-220), "Click or press any key to start!");
		DrawTextBordered(ZLV(ZLHALFW, 20), "[ALT+ENTER] Toggle Fullscreen", .75f);
		DrawTextBordered(ZL_Vector(18, 12), "(C) 2024 by Bernhard Schelling", 1, ZLRGBA(1,.9,.3,.7), ZLBLACK, 2, ZL_Origin::BottomLeft);
		ZL_Display::FillRect(0, 0, ZLWIDTH, ZLHEIGHT, ZLLUMA(0, a));
		if (ZL_Input::Down(ZLK_ESCAPE))
			ZL_Application::Quit(0);
		else if (a <= .5f && (ZL_Input::KeyDownCount() || ZL_Input::Clicked()))
		{
			InitStage(1);
			titleDone = true;
		}
		return;
	}
	else if (paused && ZL_Input::Down(ZLK_ESCAPE)) { titleTime = 0; titleDone = false; }
	else if (paused && (ZL_Input::KeyDownCount() || ZL_Input::Clicked())) paused = false;
	else if (!paused && ZL_Input::Down(ZLK_ESCAPE)) paused = true;

	#ifdef ZILLALOG
	if (ZL_Input::Down(ZLK_1)) InitStage(1);
	if (ZL_Input::Down(ZLK_2)) InitStage(2);
	if (ZL_Input::Down(ZLK_3)) InitStage(3);
	#endif

	sCreature& player = creatures[0];
	ZL_Rectf orthoRect = ZL_Rectf::FromCenter(player.Pos.x, player.Pos.y, 8 * ZLASPECTR, 8);
	#ifdef ZILLALOG
	if (ZL_Input::Held(ZLK_LSHIFT)) orthoRect = ZL_Rectf::FromCenter(MAPW*0.5f, MAPH*0.5f, MAPW*0.5f * ZLASPECTR, MAPH*0.5f);
	#endif

	int remainBugs = BugSpawnRemain, haveTinies = 0;
	for (sCreature& c : creatures)
	{
		if (!c.Health) continue;
		if (c.Type == TYPE_BUG) remainBugs++;
		if (c.Type == TYPE_TINY) haveTinies++;
	}
	const bool gameover = !haveTinies || !player.Health;
	const bool noupdate = (paused || gameover);

	ZL_Vector pursueUIPos;
	if (!noupdate)
	{
		ZL_Display::PushOrtho(orthoRect); // for ScreenToWorld

		ZL_Vector wasd = ZLV(
			((ZL_Input::Held(ZLK_LEFT) | ZL_Input::Held(ZLK_A)) ? -1.0f : 0.0f) + ((ZL_Input::Held(ZLK_RIGHT) | ZL_Input::Held(ZLK_D)) ? 1.0f : 0.0f),
			((ZL_Input::Held(ZLK_DOWN) | ZL_Input::Held(ZLK_S)) ? -1.0f : 0.0f) + ((ZL_Input::Held(ZLK_UP) | ZL_Input::Held(ZLK_W)) ? 1.0f : 0.0f));
		if (ZL_Input::Held(ZL_BUTTON_RIGHT))
			wasd = (ZL_Display::ScreenToWorld(ZL_Input::Pointer()) - player.Pos);

		if (ZL_Input::Held(ZL_BUTTON_LEFT))
		{
			fixedPursuePos = ZL_Rectf(0, 0, MAPW, MAPH).Clamp(ZL_Display::ScreenToWorld(ZL_Input::Pointer()));
			fixedPursueCreature = NULL;
			for (sCreature& c : creatures)
				if (c.Health && (c.Type & TYPEMASK_PURSUE) && c.Pos.Near(fixedPursuePos, 1))
					{ fixedPursueCreature = &c; break; }
		}

		ZL_Vector pursuePos = (fixedPursueCreature ? fixedPursueCreature->Pos : fixedPursuePos);
		pursueUIPos = ZL_Display::WorldToScreen(pursuePos);

		ZL_Display::PopOrtho();

		static float ticksum;
		for (ticksum += ZL_Math::Min(ZL_Application::Elapsed, 0.1f); ticksum >= (1.0f/60); ticksum -= (1.0f/60))
		{
			if (!!wasd) 
				UpdatePos(player, wasd.VecNorm(), 0.08f);

			if (++BugSpawnTick > BugSpawnTime && BugSpawnRemain)
			{
				sCreature* hive = NULL;
				int hives = 0;
				for (sCreature& e : creatures) { if (e.Type == TYPE_HIVE) hives++; }
				hives = RAND_INT_MAX(hives-1);
				for (sCreature& e : creatures) { if (e.Type == TYPE_HIVE && !hives--) { hive = &e; break; } }
				ZL_ASSERT(creatures.capacity() > creatures.size());
				creatures.emplace_back(TYPE_BUG, hive->Pos + ZLV(0, 0.3f));
				BugSpawnTick = 0;
				BugSpawnRemain--;
			}

			for (size_t i = creatures.size(); i--;)
			{
				sCreature& c = creatures[i];
				c.Tick++;
				if (!(c.Type & TYPEMASK_MOVE) || !c.Health)
				{
					if (c.Type == TYPE_NEWEGG && c.Tick == 20)
						c.Setup(TYPE_EGG, c.Pos);
					continue;
				}
				ZL_Vector movePos = (c.Type == TYPE_TINY ? pursuePos : player.Pos);
				ZL_Vector moveDelta = (AStarUpdate(c, movePos) - c.Pos);
				ZL_Vector moveDir = moveDelta.VecNorm();
				eType attackTypeMask = (eType)(c.Type == TYPE_TINY ? (TYPE_EGG | TYPE_BUG) : (TYPE_TINY | TYPE_PLAYER));
				float attackDistance = (c.Type == TYPE_TINY ? 1.1f : 0.5f);

				if (!c.AttackTarget)
				{
					for (sCreature& e : creatures)
					{
						if (!e.Health || !(e.Type & attackTypeMask)) continue;
						ZL_Vector ctoe = c.Pos - e.Pos;
						if (ctoe.GetLengthSq() > ZL_Math::Square(c.Radius + e.Radius + attackDistance)) continue;
						if ((ctoe | moveDir) > 0 && (c.Type != TYPE_BUG || e.AttackTarget != &c)) continue;
						c.AttackTarget = &e;
						c.Tick = RAND_INT_MAX(5); // avoid synced animation of multiple attackers
						break;
					}
				}

				if (c.AttackTarget && c.Type == TYPE_TINY)
				{
					if (c.Tick == 10 && c.AttackTarget->Health && c.AttackTarget->Type != TYPE_TINY) // don't hurt hatched tinies
					{
						sndTinyHit.Play();

						if (!--c.AttackTarget->Health)
						{
							if (c.AttackTarget->Type == TYPE_EGG)
							{
								c.AttackTarget->Setup(TYPE_TINY, c.AttackTarget->Pos); // hatch
								sndGrow.Play();
							}

							if (c.AttackTarget->Type == TYPE_BUG)
							{
								for (int spawn = 0; spawn != 3; spawn++)
								{
									ZL_ASSERT(creatures.capacity() > creatures.size());
									creatures.emplace_back(TYPE_NEWEGG, c.AttackTarget->Pos + RAND_ANGLEVEC * .25f);
								}
								sndBugDie.Play();
							}

							if (c.AttackTarget == fixedPursueCreature)
							{
								fixedPursueCreature = &player;
								for (sCreature& e : creatures)
									if (e.Health && (e.Type & TYPEMASK_PURSUE) && e.Pos.Near(c.AttackTarget->Pos, 1))
										{ fixedPursueCreature = &e; break; }
							}
						}
					}
					if (c.Tick > 20) c.AttackTarget = NULL;
				}
				else if (c.AttackTarget && c.Type == TYPE_BUG)
				{
					if (c.Tick == 15)
					{
						sndBugHit.Play();
						for (sCreature& e : creatures)
						{
							if (!e.Health || !(e.Type & attackTypeMask) || e.Pos.Far(c.AttackTarget->Pos, 0.75f)) continue;
							e.Health = ZL_Math::Max(e.Health - BugAttackDamage, 0);
							if (!e.Health) sndTinyDie.Play();
						}
					}
					if (c.Tick > 30) c.AttackTarget = NULL;
				}

				float moveSpeed = (c.Type == TYPE_TINY ? 0.08f : 0.008f);
				if (!c.AttackTarget)
				{
					if (c.Pos.Far(movePos, 1))
						UpdatePos(c, moveDir, ZL_Math::Min(moveSpeed, moveDelta.GetLength()));
				}
				else if (c.Pos.Far(c.AttackTarget->Pos, c.Radius + c.AttackTarget->Radius))
				{
					ZL_Vector dir = (c.AttackTarget->Pos - c.Pos).VecNorm();
					UpdatePos(c, dir, moveSpeed);
				}
			}
		}
	}

	ZL_Display::ClearFill();
	ZL_Display::FillGradient(0, 0, ZLWIDTH, ZLHEIGHT, ZLRGB(0,.1,0), ZLRGB(0,.2,0), ZLRGB(0,.4,.2), ZLRGB(0,.4,.1));

	ZL_Display::PushOrtho(orthoRect);
	ZL_Display::Rotate(grassSlant);
	srfGrass.DrawTo(-99, -99, 99, 99);
	ZL_Display::Rotate(-grassSlant);

	#ifdef ZILLALOG
	if (ZL_Input::Held(ZLK_LSHIFT))
	{
		for (int y = 0; y != MAPH; y++) ZL_Display::DrawLine(0, s(y), s(MAPW), s(y), ZLWHITE);
		for (int x = 0; x != MAPW; x++) ZL_Display::DrawLine(s(x), 0, s(x), s(MAPH), ZLWHITE);
	}
	#endif

	ZL_Color shadow = ZLLUMA(0, .5);
	srfWall.BatchRenderBegin(true);
	srfWall.DrawTo(-999, -999, 0.2f, 999, shadow);
	srfWall.DrawTo(0, MAPH-0.2f, MAPW, 999, shadow);
	for (int y = 0; y != MAPH; y++)
		for (int x = 0; x != MAPW; x++)
			if (Map[y*MAPW+x] == TILE_WALL)
				srfWall.DrawTo((float)x+.2f, (float)y-.2f, x+1.2f, y+.8f, shadow);
	srfWall.BatchRenderDraw();
	srfWall.DrawTo(-999, -999, 0, 999, wallColor);
	srfWall.DrawTo(0, MAPH, MAPW, 999, wallColor);
	srfWall.DrawTo(MAPW, -999, 999, 999, wallColor);
	srfWall.DrawTo(0, -999, MAPW, 0, wallColor);
	for (int y = 0; y != MAPH; y++)
		for (int x = 0; x != MAPW; x++)
			if (Map[y*MAPW+x] == TILE_WALL)
				srfWall.DrawTo((float)x, (float)y, x+1.f, y+1.f, wallColor);
	srfWall.BatchRenderEnd();

	for (sCreature& c : creatures)
		if (c.Health)
			c.UIPos = ZL_Display::WorldToScreen(c.Pos + ZLV(0, c.Radius + 0.2f));

	for (sCreature& c : creatures)
		if (c.Type == TYPE_HIVE)
			srfHive.Draw(c.Pos);

	for (sCreature& c : creatures)
		if (c.Type == TYPE_EGG)
			srfEgg.Draw(c.Pos, c.Color);

	for (sCreature& c : creatures)
		if (c.Type == TYPE_TINY && c.Health)
		{
			ZL_Vector p = c.Pos;
			if (c.AttackTarget)
			{
				p = ZL_Vector::Lerp(p, c.AttackTarget->Pos, (c.Tick < 10 ? ZL_Easing::InQuad(c.Tick / 10.f) : ZL_Easing::OutQuad((20 - c.Tick) / 10.f)));
				//ZL_Display::DrawWideLine(p, c.AttackTarget->Pos, 0.1f, ZL_Color::DarkRed, ZL_Color::Red);
			}
			float rot = ssin(c.MoveDist * 5.0f) * .25f;
			srfTiny.Draw(p, rot, c.Color);
		}

	for (sCreature& c : creatures)
		if (c.Type == TYPE_BUG && c.Health)
		{
			ZL_Vector p = c.Pos;
			if (c.AttackTarget)
			{
				p = ZL_Vector::Lerp(p, c.AttackTarget->Pos, (c.Tick < 15 ? ZL_Easing::InQuad(c.Tick / 15.f) : ZL_Easing::OutQuad((30 - c.Tick) / 15.f)));
				//ZL_Display::DrawWideLine(p, c.AttackTarget->Pos, 0.1f, ZL_Color::DarkRed, ZL_Color::Red);
			}
			float rot = ssin(c.MoveDist * 3.0f) * .25f;
			srfBug.Draw(p, rot);
		}

	for (sCreature& c : creatures)
		if (c.Type == TYPE_PLAYER && c.Health)
		{
			float rot = ssin(c.MoveDist * 5.0f) * .15f;
			float jump = ssin(c.MoveDist * 5.0f) * .1f + .1f;
			srfPlayer.Draw(c.Pos + ZLV(0, jump));
		}

	for (sCreature& c : creatures)
		if (c.Type == TYPE_NEWEGG)
		{
			float jump = ssin(c.Tick / 20.0f) * .35f;
			srfEgg.Draw(c.Pos + ZLV(0, jump), c.Color);
		}


	#ifdef ZILLALOG
	if (ZL_Input::Held(ZLK_LSHIFT))
		for (sCreature& c : creatures)
			if (c.Health && c.MoveNext != -1)
				ZL_Display::DrawLine(c.Pos, POS_FROM_TILEINDEX(c.MoveNext), ZL_Color::Green);
	#endif

	ZL_Display::PopOrtho();

	if (fixedPursueCreature != &player && !noupdate)
	{
		static sCreature* lastPursueCreature;
		static ticks_t lastPursueTick;
		if (fixedPursueCreature != lastPursueCreature || ZL_Input::Down(ZL_BUTTON_LEFT))
		{
			if (ZL_Input::Held(ZL_BUTTON_LEFT)) sndPursue.Play();
			lastPursueTick = ZLTICKS;
			lastPursueCreature = fixedPursueCreature;
		}
		float t = ZL_Easing::OutBounce(ZLSINCESECONDS(lastPursueTick));
		float f = ZL_Math::Min(t, 1.0f);
		ZL_Display::DrawCircle(pursueUIPos, 10+40*f, ZLRGBA(1,0,0, 1.6f-f), ZLRGBA(1,0,0, .4f-f*.3f));
	}
	else if (!noupdate && ZL_Input::Down(ZL_BUTTON_LEFT)) sndPursue.Play();

	ZL_Rectf screenRect(0, 0, ZLWIDTH, ZLHEIGHT), screenInnerRect = screenRect - 50;
	for (sCreature& c : creatures)
	{
		if (!c.Health) continue;

		if (c.Health != c.MaxHealth)
		{
			float healthw = 40 * c.Radius;
			ZL_Display::FillRect(ZL_Rectf::ByCorners(c.UIPos + ZLV(-healthw-1, 0), c.UIPos + ZLV(healthw+1, 6)), ZL_Color::White);
			ZL_Display::FillRect(ZL_Rectf::ByCorners(c.UIPos + ZLV(-healthw, 1), c.UIPos + ZLV(healthw, 5)), ZL_Color::DarkGreen);
			ZL_Display::FillRect(ZL_Rectf::ByCorners(c.UIPos + ZLV(-healthw, 1), c.UIPos + ZLV(ZL_Math::Lerp(-healthw, healthw, (c.Health/(float)c.MaxHealth)), 5)), ZL_Color::Green);
		}

		if (c.AttackTarget && c.Tick > 10)
		{
			fntMain.Draw(c.AttackTarget->UIPos - ZLV(0, (c.Tick - 10) * -2.0f), "-1", 1.0f, ZL_Origin::Center);
		}

		if (c.Type == TYPE_BUG && !screenRect.Contains(c.UIPos))
		{
			ZL_Vector inp = screenInnerRect.ClosestPointOnBorder(c.UIPos), dir = (c.UIPos - inp).Norm(), dirp = dir.VecPerp(), tip = inp + dir*40;
			ZL_Display::FillWideLine(inp, tip, 3, ZL_Color::Red);
			ZL_Display::FillWideLine(tip, inp + dir*20 + dirp*10, 3, ZL_Color::Red);
			ZL_Display::FillWideLine(tip, inp + dir*20 - dirp*10, 3, ZL_Color::Red);
		}
	}

	float txtzoom = (ZLSINCE(stageStartTicks) < 1000 ? (1.0f - ZL_Easing::InOutQuad(ZLSINCESECONDS(stageStartTicks))) : 0.0f);
	static ZL_String txtstr;
	static int lasttxthash;
	int txthash = (Stage ^ (remainBugs << 4) ^ (haveTinies << 12));
	if (txthash != lasttxthash) { lasttxthash = txthash; ZL_String::format(txtstr, " Bug Strength: %d \r\n Enemies Remaining: %d \r\n Tinies: %d \r\n", Stage, remainBugs, haveTinies); }
	DrawTextBordered(ZLV(10, ZLFROMH(40+txtzoom*40)), txtstr.c_str(), ZL_Math::Max(1.0f + txtzoom * 2.0f, 1.0f), ZL_Color::Yellow, ZLBLACK, 2, ZL_Origin::TopLeft);

	if (gameover)
	{
		fntBig.Draw(ZLV(ZLHALFW, ZLHALFH), "GAME OVER", 1.25f, 1.25f, ZLHSV(smod(ZLTICKS*.001f,1),.2f,1), ZL_Origin::Center);
		DrawTextBordered(ZLV(ZLHALFW, ZLHALFH - 100), "Press ESC to try again");
		DrawTextBordered(ZLV(ZLHALFW, ZLHALFH - 150), "Make sure to keep as many Tinies as possible for the next stage");
		DrawTextBordered(ZLV(ZLHALFW, ZLHALFH - 175), "Don't engage multiple enemies at once");
		DrawTextBordered(ZLV(ZLHALFW, ZLHALFH - 200), "Collect the 5 eggs in every stage before attacking");
	}
	else if (!remainBugs)
	{
		static ticks_t wintick;
		fntBig.Draw(ZLV(ZLHALFW, ZLHALFH), (Stage == 3 ? "YOU WIN" : "STAGE CLEAR"), 1.25f, 1.25f, ZLHSV(smod(ZLTICKS*.001f,1),.2f,1), ZL_Origin::Center);
		if (ZLSINCE(wintick) > 5000) wintick = ZLTICKS;
		if (Stage < 3 && ZLSINCE(wintick) > 4000) InitStage(Stage + 1);
		if (Stage == 3) DrawTextBordered(ZLV(ZLHALFW, ZLHALFH - 130), ZL_String::format("You win with %d Tinies remaining", haveTinies).c_str());
		if (Stage == 3) DrawTextBordered(ZLV(ZLHALFW, ZLHALFH - 170), "Thank you for playing!");
		if (Stage == 3) DrawTextBordered(ZLV(ZLHALFW, ZLHALFH - 250), "Press ESC to play again");
	}
	else if (paused)
	{
		ZL_Display::FillRect(0, 0, ZLWIDTH, ZLHEIGHT, ZLLUMA(0, 0.5f));
		fntBig.Draw(ZLV(ZLHALFW, ZLHALFH), "PAUSED", 1.25f, 1.25f, ZLHSV(smod(ZLTICKS*.001f,1),.2f,1), ZL_Origin::Center);
		DrawTextBordered(ZLV(ZLHALFW, ZLHALFH - 100), "Press ESC to abort round");
		DrawTextBordered(ZLV(ZLHALFW, ZLHALFH - 150), "Click or press any key to continue");
	}
	//fntMain.Draw(ZLCENTER, ZL_String::format("%d FPS - %d TICKS", (int)ZL_Application::FPS, (int)ZL_Application::ElapsedTicks).c_str());
}

static struct sTinyzilla : public ZL_Application
{
	sTinyzilla() : ZL_Application(60) { }

	virtual void Load(int argc, char *argv[])
	{
		if (!ZL_Application::LoadReleaseDesktopDataBundle()) return;
		if (!ZL_Display::Init("Tinyzilla", 1280, 720, ZL_DISPLAY_ALLOWRESIZEHORIZONTAL)) return;
		ZL_Display::ClearFill(ZL_Color::White);
		ZL_Display::SetAA(true);
		ZL_Input::Init();

		ZL_Audio::Init();
		fntMain = ZL_Font("Data/typomoderno.ttf.zip", 24.f);
		fntBig = ZL_Font("Data/typomoderno.ttf.zip", 150.f).SetCharSpacing(15);
		srfGrass = ZL_Surface("Data/grass.png").SetScale(0.03f).SetTextureRepeatMode();
		srfWall = ZL_Surface("Data/wall.png").SetScale(0.02f).SetTextureRepeatMode();
		srfPlayer = ZL_Surface("Data/player.png").SetScale(0.015f).SetOrigin(ZL_Origin::Center);
		srfTiny = ZL_Surface("Data/tiny.png").SetScale(0.0065f).SetOrigin(ZL_Origin::Center);
		srfEgg = ZL_Surface("Data/egg.png").SetScale(0.005f).SetOrigin(ZL_Origin::Center);
		srfHive = ZL_Surface("Data/hive.png").SetScale(0.01f).SetOrigin(ZL_Origin::Center);
		srfBug = ZL_Surface("Data/bug.png").SetScale(0.01f).SetOrigin(ZL_Origin::Center);

		extern TImcSongData imcDataIMCMUSIC, imcDataIMCGROW, imcDataIMCTINYHIT, imcDataIMCBUGHIT, imcDataIMCPURSUE, imcDataIMCTINYDIE, imcDataIMCBUGDIE;
		sndGrow    = ZL_SynthImcTrack::LoadAsSample(&imcDataIMCGROW);
		sndTinyHit = ZL_SynthImcTrack::LoadAsSample(&imcDataIMCTINYHIT);
		sndBugHit  = ZL_SynthImcTrack::LoadAsSample(&imcDataIMCBUGHIT);
		sndPursue  = ZL_SynthImcTrack::LoadAsSample(&imcDataIMCPURSUE);
		sndTinyDie = ZL_SynthImcTrack::LoadAsSample(&imcDataIMCTINYDIE);
		sndBugDie  = ZL_SynthImcTrack::LoadAsSample(&imcDataIMCBUGDIE);
		imcMusic = ZL_SynthImcTrack(&imcDataIMCMUSIC);
		imcMusic.Play();
	}

	virtual void AfterFrame()
	{
		::Update();
	}
} Tinyzilla;

#if 1 // MUSIC/SOUND DATA
static const unsigned int IMCMUSIC_OrderTable[] = {
	0x000000001, 0x000000001, 0x010000001, 0x020000001, 0x030000001, 0x030000011, 0x030000010, 0x030000002,
	0x030000003, 0x030000012, 0x030000023, 0x030000032, 0x030000033, 0x030000000, 0x040000004,
};
static const unsigned char IMCMUSIC_PatternData[] = {
	0x50, 0, 0, 0x49, 0x47, 0x45, 0, 0, 0x54, 0, 0, 0x4B, 0x49, 0x47, 0, 0,
	0x55, 0, 0, 0, 0x57, 0, 0, 0, 0x5B, 0x5B, 0x5B, 0, 0x57, 0, 0, 0,
	0x55, 0, 0, 0, 0x57, 0, 0, 0, 0x60, 0x60, 0x60, 0, 0x57, 0, 0, 0,
	0, 0, 0, 0, 255, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
	0x50, 0, 0, 0x50, 0x52, 0x50, 0, 0, 0x54, 0, 0, 0x55, 0x57, 0x55, 0, 0,
	0x60, 0x5B, 0x57, 0, 0x60, 0x5B, 0x57, 0, 0x60, 0x5B, 0x57, 0, 0x60, 0x5B, 0x57, 0,
	0x40, 0x57, 0x40, 0x57, 0x40, 0x57, 0x40, 0x57, 0x40, 0x57, 0x40, 0x57, 0x40, 0x57, 0x40, 0x57,
	0x50, 0, 0x50, 0, 0x50, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
	0x50, 0, 0x50, 0, 0x50, 0, 0, 0, 0x50, 0, 0x50, 0, 0x50, 0, 0, 0,
	0x50, 0, 0x50, 0, 0x50, 0, 0x50, 0, 0x50, 0, 0x50, 0, 0x50, 0, 0x50, 0,
	0x55, 0, 0, 0, 0x55, 0, 0, 0, 0x55, 0, 0, 0, 0, 0, 0, 0,
};
static const unsigned char IMCMUSIC_PatternLookupTable[] = { 0, 4, 7, 7, 7, 7, 7, 7, };
static const TImcSongEnvelope IMCMUSIC_EnvList[] = {
	{ 50, 100, 202, 24, 255, 255, true, 255, },
	{ 0, 256, 2, 27, 13, 255, false, 255, },
	{ 0, 256, 157, 25, 15, 255, false, 0, },
	{ 0, 256, 204, 8, 16, 4, true, 255, },
	{ 0, 256, 209, 8, 16, 255, true, 255, },
	{ 64, 256, 261, 8, 15, 255, true, 255, },
	{ 0, 256, 523, 8, 15, 255, true, 255, },
	{ 0, 256, 2092, 8, 16, 255, true, 255, },
	{ 0, 256, 523, 8, 16, 255, true, 255, },
	{ 32, 256, 196, 8, 16, 255, true, 255, },
};
static TImcSongEnvelopeCounter IMCMUSIC_EnvCounterList[] = {
	{ -1, -1, 256 }, { 0, 0, 50 }, { 1, 0, 18 }, { 2, 0, 2 },
	{ 3, 1, 256 }, { 4, 1, 256 }, { 5, 1, 256 }, { 4, 1, 256 },
	{ 6, 1, 256 }, { 7, 1, 256 }, { 8, 7, 256 }, { 9, 7, 256 },
};
static const TImcSongOscillator IMCMUSIC_OscillatorList[] = {
	{ 7, 0, IMCSONGOSCTYPE_SINE, 0, -1, 208, 0, 0 },
	{ 8, 0, IMCSONGOSCTYPE_SINE, 0, -1, 255, 0, 0 },
	{ 7, 0, IMCSONGOSCTYPE_SINE, 0, -1, 255, 0, 0 },
	{ 9, 0, IMCSONGOSCTYPE_SQUARE, 0, 0, 30, 0, 0 },
	{ 7, 0, IMCSONGOSCTYPE_SAW, 0, 1, 136, 0, 0 },
	{ 6, 0, IMCSONGOSCTYPE_SINE, 1, -1, 114, 5, 6 },
	{ 8, 0, IMCSONGOSCTYPE_SINE, 1, -1, 12, 7, 8 },
	{ 8, 0, IMCSONGOSCTYPE_NOISE, 1, -1, 116, 9, 0 },
	{ 7, 0, IMCSONGOSCTYPE_NOISE, 1, 5, 10, 0, 0 },
	{ 8, 0, IMCSONGOSCTYPE_SINE, 2, -1, 100, 0, 0 },
	{ 8, 0, IMCSONGOSCTYPE_SINE, 3, -1, 100, 0, 0 },
	{ 8, 0, IMCSONGOSCTYPE_SINE, 4, -1, 100, 0, 0 },
	{ 8, 0, IMCSONGOSCTYPE_SINE, 5, -1, 100, 0, 0 },
	{ 8, 0, IMCSONGOSCTYPE_SINE, 6, -1, 100, 0, 0 },
	{ 8, 0, IMCSONGOSCTYPE_NOISE, 7, -1, 127, 0, 11 },
};
static const TImcSongEffect IMCMUSIC_EffectList[] = {
	{ 0, 0, 101, 0, IMCSONGEFFECTTYPE_FLANGE, 1, 0 },
	{ 92, 0, 1, 0, IMCSONGEFFECTTYPE_LOWPASS, 0, 0 },
	{ 255, 212, 1, 0, IMCSONGEFFECTTYPE_RESONANCE, 2, 3 },
	{ 122, 0, 16536, 0, IMCSONGEFFECTTYPE_DELAY, 0, 0 },
	{ 9906, 843, 1, 1, IMCSONGEFFECTTYPE_OVERDRIVE, 0, 0 },
	{ 29, 56, 1, 1, IMCSONGEFFECTTYPE_RESONANCE, 0, 0 },
	{ 122, 0, 5512, 7, IMCSONGEFFECTTYPE_DELAY, 0, 0 },
	{ 255, 156, 1, 7, IMCSONGEFFECTTYPE_RESONANCE, 0, 0 },
	{ 227, 0, 1, 7, IMCSONGEFFECTTYPE_HIGHPASS, 0, 0 },
};
static unsigned char IMCMUSIC_ChannelVol[8] = { 30, 79, 100, 100, 100, 100, 100, 212 };
static const unsigned char IMCMUSIC_ChannelEnvCounter[8] = { 0, 4, 0, 0, 0, 0, 0, 10 };
static const bool IMCMUSIC_ChannelStopNote[8] = { true, false, false, false, false, false, false, true };
TImcSongData imcDataIMCMUSIC = {
	/*LEN*/ 0xF, /*ROWLENSAMPLES*/ 5512, /*ENVLISTSIZE*/ 10, /*ENVCOUNTERLISTSIZE*/ 12, /*OSCLISTSIZE*/ 15, /*EFFECTLISTSIZE*/ 9, /*VOL*/ 35,
	IMCMUSIC_OrderTable, IMCMUSIC_PatternData, IMCMUSIC_PatternLookupTable, IMCMUSIC_EnvList, IMCMUSIC_EnvCounterList, IMCMUSIC_OscillatorList, IMCMUSIC_EffectList,
	IMCMUSIC_ChannelVol, IMCMUSIC_ChannelEnvCounter, IMCMUSIC_ChannelStopNote };

static const unsigned int IMCGROW_OrderTable[] = {
	0x000000001,
};
static const unsigned char IMCGROW_PatternData[] = {
	0x50, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
};
static const unsigned char IMCGROW_PatternLookupTable[] = { 0, 1, 1, 1, 1, 1, 1, 1, };
static const TImcSongEnvelope IMCGROW_EnvList[] = {
	{ 0, 256, 42, 8, 16, 255, true, 255, },
	{ 50, 256, 15, 24, 11, 255, true, 255, },
	{ 100, 200, 523, 0, 64, 255, false, 255, },
};
static TImcSongEnvelopeCounter IMCGROW_EnvCounterList[] = {
	{ 0, 0, 256 }, { -1, -1, 256 }, { 1, 0, 50 }, { 2, 0, 150 },
};
static const TImcSongOscillator IMCGROW_OscillatorList[] = {
	{ 8, 0, IMCSONGOSCTYPE_SQUARE, 0, -1, 100, 1, 2 },
	{ 8, 0, IMCSONGOSCTYPE_SINE, 1, -1, 100, 0, 0 },
	{ 8, 0, IMCSONGOSCTYPE_SINE, 2, -1, 100, 0, 0 },
	{ 8, 0, IMCSONGOSCTYPE_SINE, 3, -1, 100, 0, 0 },
	{ 8, 0, IMCSONGOSCTYPE_SINE, 4, -1, 100, 0, 0 },
	{ 8, 0, IMCSONGOSCTYPE_SINE, 5, -1, 100, 0, 0 },
	{ 8, 0, IMCSONGOSCTYPE_SINE, 6, -1, 100, 0, 0 },
	{ 8, 0, IMCSONGOSCTYPE_SINE, 7, -1, 100, 0, 0 },
};
static const TImcSongEffect IMCGROW_EffectList[] = {
	{ 0, 0, 201, 0, IMCSONGEFFECTTYPE_FLANGE, 3, 0 },
};
static unsigned char IMCGROW_ChannelVol[8] = { 100, 100, 100, 100, 100, 100, 100, 100 };
static const unsigned char IMCGROW_ChannelEnvCounter[8] = { 0, 0, 0, 0, 0, 0, 0, 0 };
static const bool IMCGROW_ChannelStopNote[8] = { true, false, false, false, false, false, false, false };
TImcSongData imcDataIMCGROW = {
	/*LEN*/ 0x1, /*ROWLENSAMPLES*/ 2594, /*ENVLISTSIZE*/ 3, /*ENVCOUNTERLISTSIZE*/ 4, /*OSCLISTSIZE*/ 8, /*EFFECTLISTSIZE*/ 1, /*VOL*/ 60,
	IMCGROW_OrderTable, IMCGROW_PatternData, IMCGROW_PatternLookupTable, IMCGROW_EnvList, IMCGROW_EnvCounterList, IMCGROW_OscillatorList, IMCGROW_EffectList,
	IMCGROW_ChannelVol, IMCGROW_ChannelEnvCounter, IMCGROW_ChannelStopNote };

static const unsigned int IMCTINYHIT_OrderTable[] = {
	0x000000001,
};
static const unsigned char IMCTINYHIT_PatternData[] = {
	0x50, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
};
static const unsigned char IMCTINYHIT_PatternLookupTable[] = { 0, 1, 1, 1, 1, 1, 1, 1, };
static const TImcSongEnvelope IMCTINYHIT_EnvList[] = {
	{ 0, 256, 379, 8, 16, 255, true, 255, },
	{ 32, 256, 196, 8, 16, 255, true, 255, },
	{ 0, 256, 277, 10, 19, 255, true, 255, },
	{ 0, 256, 65, 8, 10, 255, true, 255, },
};
static TImcSongEnvelopeCounter IMCTINYHIT_EnvCounterList[] = {
	{ 0, 0, 256 }, { -1, -1, 256 }, { 1, 0, 256 }, { 2, 0, 248 },
	{ 3, 0, 256 },
};
static const TImcSongOscillator IMCTINYHIT_OscillatorList[] = {
	{ 8, 0, IMCSONGOSCTYPE_NOISE, 0, -1, 76, 1, 2 },
	{ 8, 0, IMCSONGOSCTYPE_SINE, 0, -1, 204, 1, 3 },
	{ 8, 0, IMCSONGOSCTYPE_SINE, 1, -1, 100, 0, 0 },
	{ 8, 0, IMCSONGOSCTYPE_SINE, 2, -1, 100, 0, 0 },
	{ 8, 0, IMCSONGOSCTYPE_SINE, 3, -1, 100, 0, 0 },
	{ 8, 0, IMCSONGOSCTYPE_SINE, 4, -1, 100, 0, 0 },
	{ 8, 0, IMCSONGOSCTYPE_SINE, 5, -1, 100, 0, 0 },
	{ 8, 0, IMCSONGOSCTYPE_SINE, 6, -1, 100, 0, 0 },
	{ 8, 0, IMCSONGOSCTYPE_SINE, 7, -1, 100, 0, 0 },
};
static const TImcSongEffect IMCTINYHIT_EffectList[] = {
	{ 128, 0, 3034, 0, IMCSONGEFFECTTYPE_DELAY, 0, 0 },
	{ 134, 110, 1, 0, IMCSONGEFFECTTYPE_RESONANCE, 1, 1 },
	{ 220, 0, 1, 0, IMCSONGEFFECTTYPE_HIGHPASS, 1, 0 },
	{ 3175, 897, 1, 0, IMCSONGEFFECTTYPE_OVERDRIVE, 0, 4 },
};
static unsigned char IMCTINYHIT_ChannelVol[8] = { 107, 100, 100, 100, 100, 100, 100, 100 };
static const unsigned char IMCTINYHIT_ChannelEnvCounter[8] = { 0, 0, 0, 0, 0, 0, 0, 0 };
static const bool IMCTINYHIT_ChannelStopNote[8] = { true, false, false, false, false, false, false, false };
TImcSongData imcDataIMCTINYHIT = {
	/*LEN*/ 0x1, /*ROWLENSAMPLES*/ 2594, /*ENVLISTSIZE*/ 4, /*ENVCOUNTERLISTSIZE*/ 5, /*OSCLISTSIZE*/ 9, /*EFFECTLISTSIZE*/ 4, /*VOL*/ 100,
	IMCTINYHIT_OrderTable, IMCTINYHIT_PatternData, IMCTINYHIT_PatternLookupTable, IMCTINYHIT_EnvList, IMCTINYHIT_EnvCounterList, IMCTINYHIT_OscillatorList, IMCTINYHIT_EffectList,
	IMCTINYHIT_ChannelVol, IMCTINYHIT_ChannelEnvCounter, IMCTINYHIT_ChannelStopNote };

static const unsigned int IMCBUGHIT_OrderTable[] = {
	0x000000001,
};
static const unsigned char IMCBUGHIT_PatternData[] = {
	0x50, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
};
static const unsigned char IMCBUGHIT_PatternLookupTable[] = { 0, 1, 1, 1, 1, 1, 1, 1, };
static const TImcSongEnvelope IMCBUGHIT_EnvList[] = {
	{ 0, 256, 65, 8, 16, 4, true, 255, },
	{ 0, 256, 277, 9, 15, 255, true, 255, },
	{ 0, 256, 137, 3, 21, 255, true, 255, },
	{ 0, 256, 184, 7, 17, 255, true, 255, },
};
static TImcSongEnvelopeCounter IMCBUGHIT_EnvCounterList[] = {
	{ 0, 0, 256 }, { 1, 0, 254 }, { -1, -1, 256 }, { 2, 0, 206 },
	{ -1, -1, 128 }, { 3, 0, 254 },
};
static const TImcSongOscillator IMCBUGHIT_OscillatorList[] = {
	{ 7, 0, IMCSONGOSCTYPE_SQUARE, 0, -1, 104, 1, 2 },
	{ 7, 0, IMCSONGOSCTYPE_SQUARE, 0, -1, 32, 3, 2 },
	{ 8, 0, IMCSONGOSCTYPE_NOISE, 0, -1, 100, 5, 2 },
	{ 7, 0, IMCSONGOSCTYPE_SAW, 0, 0, 20, 2, 2 },
	{ 2, 31, IMCSONGOSCTYPE_SINE, 0, 1, 2, 4, 4 },
	{ 8, 0, IMCSONGOSCTYPE_SINE, 1, -1, 100, 0, 0 },
	{ 8, 0, IMCSONGOSCTYPE_SINE, 2, -1, 100, 0, 0 },
	{ 8, 0, IMCSONGOSCTYPE_SINE, 3, -1, 100, 0, 0 },
	{ 8, 0, IMCSONGOSCTYPE_SINE, 4, -1, 100, 0, 0 },
	{ 8, 0, IMCSONGOSCTYPE_SINE, 5, -1, 100, 0, 0 },
	{ 8, 0, IMCSONGOSCTYPE_SINE, 6, -1, 100, 0, 0 },
	{ 8, 0, IMCSONGOSCTYPE_SINE, 7, -1, 100, 0, 0 },
};
static const TImcSongEffect IMCBUGHIT_EffectList[] = {
	{ 44, 0, 5188, 0, IMCSONGEFFECTTYPE_DELAY, 0, 0 },
	{ 47, 181, 1, 0, IMCSONGEFFECTTYPE_RESONANCE, 2, 2 },
};
static unsigned char IMCBUGHIT_ChannelVol[8] = { 97, 100, 100, 100, 100, 100, 100, 100 };
static const unsigned char IMCBUGHIT_ChannelEnvCounter[8] = { 0, 0, 0, 0, 0, 0, 0, 0 };
static const bool IMCBUGHIT_ChannelStopNote[8] = { false, false, false, false, false, false, false, false };
TImcSongData imcDataIMCBUGHIT = {
	/*LEN*/ 0x1, /*ROWLENSAMPLES*/ 2594, /*ENVLISTSIZE*/ 4, /*ENVCOUNTERLISTSIZE*/ 6, /*OSCLISTSIZE*/ 12, /*EFFECTLISTSIZE*/ 2, /*VOL*/ 100,
	IMCBUGHIT_OrderTable, IMCBUGHIT_PatternData, IMCBUGHIT_PatternLookupTable, IMCBUGHIT_EnvList, IMCBUGHIT_EnvCounterList, IMCBUGHIT_OscillatorList, IMCBUGHIT_EffectList,
	IMCBUGHIT_ChannelVol, IMCBUGHIT_ChannelEnvCounter, IMCBUGHIT_ChannelStopNote };

static const unsigned int IMCPURSUE_OrderTable[] = {
	0x000000001,
};
static const unsigned char IMCPURSUE_PatternData[] = {
	0x50, 0, 0, 0, 255, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
};
static const unsigned char IMCPURSUE_PatternLookupTable[] = { 0, 1, 1, 1, 1, 1, 1, 1, };
static const TImcSongEnvelope IMCPURSUE_EnvList[] = {
	{ 0, 256, 69, 2, 22, 6, true, 255, },
	{ 0, 256, 699, 25, 255, 255, true, 255, },
};
static TImcSongEnvelopeCounter IMCPURSUE_EnvCounterList[] = {
	{ 0, 0, 184 }, { 1, 0, 2 }, { -1, -1, 256 }, { 1, 0, 2 },
};
static const TImcSongOscillator IMCPURSUE_OscillatorList[] = {
	{ 8, 150, IMCSONGOSCTYPE_SAW, 0, -1, 102, 1, 2 },
	{ 8, 200, IMCSONGOSCTYPE_SQUARE, 0, -1, 66, 3, 2 },
	{ 8, 0, IMCSONGOSCTYPE_NOISE, 0, 0, 12, 2, 2 },
	{ 8, 0, IMCSONGOSCTYPE_NOISE, 0, 1, 12, 2, 2 },
	{ 8, 0, IMCSONGOSCTYPE_SINE, 1, -1, 100, 0, 0 },
	{ 8, 0, IMCSONGOSCTYPE_SINE, 2, -1, 100, 0, 0 },
	{ 8, 0, IMCSONGOSCTYPE_SINE, 3, -1, 100, 0, 0 },
	{ 8, 0, IMCSONGOSCTYPE_SINE, 4, -1, 100, 0, 0 },
	{ 8, 0, IMCSONGOSCTYPE_SINE, 5, -1, 100, 0, 0 },
	{ 8, 0, IMCSONGOSCTYPE_SINE, 6, -1, 100, 0, 0 },
	{ 8, 0, IMCSONGOSCTYPE_SINE, 7, -1, 100, 0, 0 },
};
static const TImcSongEffect IMCPURSUE_EffectList[] = {
	{ 67, 0, 1, 0, IMCSONGEFFECTTYPE_LOWPASS, 2, 0 },
};
static unsigned char IMCPURSUE_ChannelVol[8] = { 100, 100, 100, 100, 100, 100, 100, 100 };
static const unsigned char IMCPURSUE_ChannelEnvCounter[8] = { 0, 0, 0, 0, 0, 0, 0, 0 };
static const bool IMCPURSUE_ChannelStopNote[8] = { false, false, false, false, false, false, false, false };
TImcSongData imcDataIMCPURSUE = {
	/*LEN*/ 0x1, /*ROWLENSAMPLES*/ 2594, /*ENVLISTSIZE*/ 2, /*ENVCOUNTERLISTSIZE*/ 4, /*OSCLISTSIZE*/ 11, /*EFFECTLISTSIZE*/ 1, /*VOL*/ 100,
	IMCPURSUE_OrderTable, IMCPURSUE_PatternData, IMCPURSUE_PatternLookupTable, IMCPURSUE_EnvList, IMCPURSUE_EnvCounterList, IMCPURSUE_OscillatorList, IMCPURSUE_EffectList,
	IMCPURSUE_ChannelVol, IMCPURSUE_ChannelEnvCounter, IMCPURSUE_ChannelStopNote };

static const unsigned int IMCTINYDIE_OrderTable[] = {
	0x000000001,
};
static const unsigned char IMCTINYDIE_PatternData[] = {
	0x50, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
};
static const unsigned char IMCTINYDIE_PatternLookupTable[] = { 0, 1, 1, 1, 1, 1, 1, 1, };
static const TImcSongEnvelope IMCTINYDIE_EnvList[] = {
	{ 0, 256, 15, 8, 16, 255, true, 255, },
	{ 0, 256, 14, 7, 15, 255, true, 255, },
	{ 118, 138, 1046, 8, 255, 255, true, 255, },
};
static TImcSongEnvelopeCounter IMCTINYDIE_EnvCounterList[] = {
	{ 0, 0, 256 }, { -1, -1, 256 }, { 1, 0, 254 }, { 2, 0, 138 },
};
static const TImcSongOscillator IMCTINYDIE_OscillatorList[] = {
	{ 9, 66, IMCSONGOSCTYPE_SINE, 0, -1, 100, 1, 2 },
	{ 8, 0, IMCSONGOSCTYPE_SINE, 0, 0, 72, 1, 3 },
	{ 8, 0, IMCSONGOSCTYPE_SINE, 1, -1, 100, 0, 0 },
	{ 8, 0, IMCSONGOSCTYPE_SINE, 2, -1, 100, 0, 0 },
	{ 8, 0, IMCSONGOSCTYPE_SINE, 3, -1, 100, 0, 0 },
	{ 8, 0, IMCSONGOSCTYPE_SINE, 4, -1, 100, 0, 0 },
	{ 8, 0, IMCSONGOSCTYPE_SINE, 5, -1, 100, 0, 0 },
	{ 8, 0, IMCSONGOSCTYPE_SINE, 6, -1, 100, 0, 0 },
	{ 8, 0, IMCSONGOSCTYPE_SINE, 7, -1, 100, 0, 0 },
};
static unsigned char IMCTINYDIE_ChannelVol[8] = { 100, 100, 100, 100, 100, 100, 100, 100 };
static const unsigned char IMCTINYDIE_ChannelEnvCounter[8] = { 0, 0, 0, 0, 0, 0, 0, 0 };
static const bool IMCTINYDIE_ChannelStopNote[8] = { true, false, false, false, false, false, false, false };
TImcSongData imcDataIMCTINYDIE = {
	/*LEN*/ 0x1, /*ROWLENSAMPLES*/ 8268, /*ENVLISTSIZE*/ 3, /*ENVCOUNTERLISTSIZE*/ 4, /*OSCLISTSIZE*/ 9, /*EFFECTLISTSIZE*/ 0, /*VOL*/ 100,
	IMCTINYDIE_OrderTable, IMCTINYDIE_PatternData, IMCTINYDIE_PatternLookupTable, IMCTINYDIE_EnvList, IMCTINYDIE_EnvCounterList, IMCTINYDIE_OscillatorList, NULL,
	IMCTINYDIE_ChannelVol, IMCTINYDIE_ChannelEnvCounter, IMCTINYDIE_ChannelStopNote };

static const unsigned int IMCBUGDIE_OrderTable[] = {
	0x000000001,
};
static const unsigned char IMCBUGDIE_PatternData[] = {
	0x32, 255, 0x30, 255, 0x29, 0, 0, 0, 255, 0, 0, 0, 0, 0, 0, 0,
};
static const unsigned char IMCBUGDIE_PatternLookupTable[] = { 0, 1, 1, 1, 1, 1, 1, 1, };
static const TImcSongEnvelope IMCBUGDIE_EnvList[] = {
	{ 0, 256, 28, 5, 19, 15, true, 255, },
	{ 0, 256, 14, 7, 15, 255, true, 255, },
	{ 118, 138, 1046, 8, 255, 255, true, 255, },
};
static TImcSongEnvelopeCounter IMCBUGDIE_EnvCounterList[] = {
	{ 0, 0, 238 }, { -1, -1, 256 }, { 1, 0, 254 }, { 2, 0, 138 },
};
static const TImcSongOscillator IMCBUGDIE_OscillatorList[] = {
	{ 9, 66, IMCSONGOSCTYPE_SINE, 0, -1, 100, 1, 2 },
	{ 8, 0, IMCSONGOSCTYPE_SINE, 0, 0, 72, 1, 3 },
	{ 8, 0, IMCSONGOSCTYPE_SINE, 1, -1, 100, 0, 0 },
	{ 8, 0, IMCSONGOSCTYPE_SINE, 2, -1, 100, 0, 0 },
	{ 8, 0, IMCSONGOSCTYPE_SINE, 3, -1, 100, 0, 0 },
	{ 8, 0, IMCSONGOSCTYPE_SINE, 4, -1, 100, 0, 0 },
	{ 8, 0, IMCSONGOSCTYPE_SINE, 5, -1, 100, 0, 0 },
	{ 8, 0, IMCSONGOSCTYPE_SINE, 6, -1, 100, 0, 0 },
	{ 8, 0, IMCSONGOSCTYPE_SINE, 7, -1, 100, 0, 0 },
};
static unsigned char IMCBUGDIE_ChannelVol[8] = { 100, 100, 100, 100, 100, 100, 100, 100 };
static const unsigned char IMCBUGDIE_ChannelEnvCounter[8] = { 0, 0, 0, 0, 0, 0, 0, 0 };
static const bool IMCBUGDIE_ChannelStopNote[8] = { false, false, false, false, false, false, false, false };
TImcSongData imcDataIMCBUGDIE = {
	/*LEN*/ 0x1, /*ROWLENSAMPLES*/ 4410, /*ENVLISTSIZE*/ 3, /*ENVCOUNTERLISTSIZE*/ 4, /*OSCLISTSIZE*/ 9, /*EFFECTLISTSIZE*/ 0, /*VOL*/ 100,
	IMCBUGDIE_OrderTable, IMCBUGDIE_PatternData, IMCBUGDIE_PatternLookupTable, IMCBUGDIE_EnvList, IMCBUGDIE_EnvCounterList, IMCBUGDIE_OscillatorList, NULL,
	IMCBUGDIE_ChannelVol, IMCBUGDIE_ChannelEnvCounter, IMCBUGDIE_ChannelStopNote };


#endif
