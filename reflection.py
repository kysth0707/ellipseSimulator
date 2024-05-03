import math
import time
import pygame
# import matplotlib.pyplot as plt
# from random import random
# from matplotlib.patches import Ellipse

def tan(d): return math.tan(math.radians(d))
def sin(d): return math.sin(math.radians(d))
def cos(d): return math.cos(math.radians(d))
def atan(n): return math.degrees(math.atan(n))

# def random_point(a, b):
#     d = random()*360
#     return (a * cos(d) * random(), b * sin(d) * random())

SPECIAL = (-360, -270, -180, -90, 0, 90, 180, 270, 360)
SPECIAL_ANGLES = [tan(i) for i in SPECIAL]
NINTIES = ('HORIZONTAL', 'VERTICAL')

def make_ellipse(a, d):
	assert 0 < d < 45
	b = a * tan(d)
	return (a, b)

def make_line(pos, d):
	x, y = pos
	if d in SPECIAL:
		if d in (-270, -90, 90, 270):
			return ('VERTICAL', x)
		return ('HORIZONTAL', y)
	k = tan(d)
	c = -x*k + y
	return (k, c)

def intersection(k, c, a, b):
	assert c**2 < a**2 * k**2 + b**2
	n1 = a**2 * k**2 + b**2
	n2 = 2 * a**2 * k * c
	n3 = a**2 * (c**2 - b**2)
	n4 = (n2**2 - 4 * n1 * n3) ** .5
	x0 = (-n2 + n4) / (2 * n1)
	x1 = (-n2 - n4) / (2 * n1)
	y0 = k * x0 + c
	y1 = k * x1 + c
	return [(x0, y0), (x1, y1)]

def special_intersection(dimension, value, a, b):
	assert dimension in NINTIES
	if dimension == 'VERTICAL':
		x = value
		assert abs(x) < a
		y0 = (b**2 - x**2 * b**2 / a**2) ** .5
		return [(x, y0), (x, -y0)]
	y = value
	assert abs(y) < b
	x0 = (a**2 - y**2 * a**2 / b**2) ** .5
	return [(x0, y), (-x0, y)]
        

def tangent(x, y, a, b):
	assert math.isclose(x**2 / a**2 + y**2 / b**2, 1)
	k = -x * b**2 / (a**2 * y)
	if k not in SPECIAL_ANGLES:
		c = b**2 / y
		return (k, c)
	if SPECIAL_ANGLES.index(k) in (1, 3, 5, 7):
		return ('VERTICAL', x)
	return ('HORIZONTAL', y)

def perpendicular(k, x, y):
	k1 = -1/k
	c = y - k1*x
	return (k1, c)

def special_perpendicular(dimension, x, y):
	assert dimension in NINTIES
	if dimension == 'VERTICAL':
		return ('HORIZONTAL', y)
	return ('VERTICAL', x)

def reflect(k1, k2, x, y):
	a1 = atan(k1)
	a2 = atan(k2)
	diff_a = a2 - a1
	diff_a = (diff_a + 180) % 360 - 180
	a3 = a2 + diff_a
	if a3 not in SPECIAL:
		k = tan(a3)
		c = y - k * x
		return (k, c)
	if a3 in (-270, -90, 90, 270):
		return ('VERTICAL', x)
	return ('HORIZONTAL', y)

def special_reflect(dimension, k, x, y, reverse=False):
	assert dimension in NINTIES
	a = atan(k)
	if not reverse:
		diff_a = a - 90 if dimension == 'VERTICAL' else a - 180
	else:
		diff_a = 90 - a if dimension == 'VERTICAL' else 180 - a
	diff_a = (diff_a + 180) % 360 - 180
	a1 = a + diff_a
	k = tan(a1)
	c = y - k * x
	return (k, c)

def bounce(k1, x, y, a, b):
	tan_k, tan_c = tangent(x, y, a, b)
	if tan_k not in NINTIES:
		perp_func = perpendicular
	else:
		perp_func = special_perpendicular

	perp_k, perp_c = perp_func(tan_k, x, y)

	if perp_k not in NINTIES and k1 not in NINTIES:
		refl_k, refl_c = reflect(k1, perp_k, x, y)
	else:
		reverse = False
		if perp_k in NINTIES:
			reverse = True
		refl_k, refl_c = special_reflect(k1, perp_k, x, y, reverse)

	if refl_k not in NINTIES:
		inte_func = intersection
	else:
		inte_func = special_intersection

	intersects = inte_func(refl_k, refl_c, a, b)
	index = 1
	new_x, new_y = intersects[0]
	if not math.isclose(new_x, x) and not math.isclose(new_y, y):
		index = 0

	next_x, next_y = intersects[index]
	return (refl_k, refl_c, next_x, next_y)
        

def recursive_reflect(a, b, pos=None, angle=None, iterations=360, SCALE=1):
	"""
	- a : ?
	- b : ?
	- pos : 시작위치
	- angle : 출발 각도
	- iterations : 반사 횟수

	return segments
	- segments : [(시작x, 시작y), (도착x, 도착y)]
	"""
	init_x, init_y = pos
	assert init_x**2 / a**2 + init_y**2 / b**2 <= 1

	segments = []

	k, c = make_line(pos, angle)
	if k not in NINTIES:
		func = intersection
	else:
		func = special_intersection

	intersects = func(k, c, a, b)
	index = 1
	if 0 <= angle < 90 or 270 <= angle < 360:
		if intersects[0][0] >= init_x:
			index = 0

	elif intersects[0][0] <= init_x:
		index = 0

	sect_x, sect_y = intersects[index]

	segments.append([(init_x * SCALE, init_y * SCALE), (sect_x * SCALE, sect_y * SCALE)])

	start_x, start_y = sect_x, sect_y
	current_k = k
	for _ in range(iterations):
		refl_k, refl_c, next_x, next_y = bounce(current_k, start_x, start_y, a, b)
		segments.append([(start_x * SCALE, start_y * SCALE), (next_x * SCALE, next_y * SCALE)])
		
		start_x, start_y = next_x, next_y
		current_k = refl_k
	# print(segments)
	return segments

# def plot_reflections(a=4, d=30, iterations=360):
# 	a, b = make_ellipse(a, d)
# 	segments = recursive_reflect(a, b, (0, 0), 20, iterations)
# 	fig = plt.figure(frameon=False)
# 	ax = fig.add_subplot(1,1,1)
# 	ax.set_axis_off()
# 	ax.add_patch(Ellipse((0, 0), 2*a, 2*b, edgecolor='k', fc='None', lw=2))
# 	for segment in segments:
# 		x, y = zip(*segment)
# 		ax.plot(x, y)
# 	fig.subplots_adjust(left=0, bottom=0, right=1, top=1, wspace=0, hspace=0)
# 	plt.axis('scaled')
# 	plt.box(False)
# 	ax = plt.gca()
# 	ax.set_xlim([-a, a])
# 	ax.set_ylim([-b, b])
# 	plt.show()


originala = 4
originald = 30
startPos = (0, 0)

originala, originalb = make_ellipse(originala, originald)



# ============ 비율 맞춰주기
SCALE = 150

segments = recursive_reflect(originala, originalb, startPos, 20, 200, SCALE)


# =================== 실제 시작 및 변수 리셋
pygame.init()


BACKGROUND_COLOR = (0, 0, 0)
ELLIPSE_COLOR = (255, 255, 255)
LINE_COLOR = (255, 255, 0)

FPS_FONT = pygame.font.SysFont("malgungothic", 25, True)

lastMouseX, lastMouseY = (-1, -1)
ScreenWidth = 1600
ScreenHeight = 900
screen = pygame.display.set_mode((ScreenWidth, ScreenHeight))
pygame.display.set_caption('타원 반사')


def toPyPlane(pos):
	return (int(ScreenWidth / 2 + pos[0]), int(ScreenHeight / 2 - pos[1]))

# =========== 화면 반복

lastTime = time.time()
clock = pygame.time.Clock()
run = True
while run:
	# clock.tick(60)

	# ================ 화면 그리기
	screen.fill(BACKGROUND_COLOR)


	dt = time.time() - lastTime
	if dt != 0:
		screen.blit(FPS_FONT.render(f"{int(1/dt)} FPS", True, LINE_COLOR), (10, 10))
	lastTime = time.time()


	q,w = toPyPlane((-originala*SCALE, originalb*SCALE))
	ellipseRect = pygame.Rect(q,w, 2*originala*SCALE, 2*originalb*SCALE)
	pygame.draw.ellipse(screen, ELLIPSE_COLOR, ellipseRect, 3)

	for segment in segments:
		start, end = segment
		pygame.draw.line(screen, LINE_COLOR, toPyPlane(start), toPyPlane(end))

	pygame.display.update()

	# ================ 키 처리
	for event in pygame.event.get():
		if event.type == pygame.QUIT:
			run = False
			pygame.quit()
		# elif event.type == pygame.KEYDOWN:
		# 	if event.key == pygame.K_LEFT: #왼쪽
		# 		if cursorPos > 0:
		# 			cursorPos -= 1
		# 			helpPos = 0
		# 	elif event.key == pygame.K_RIGHT: #오른쪽
		# 		if cursorPos < len(formulaData):
		# 			cursorPos += 1
		# 			helpPos = 0

	# ============ 빛 재 생성?
	mouseX, mouseY = pygame.mouse.get_pos()
	if lastMouseX != mouseX or lastMouseY != mouseY:
		# 갱신 필요
		mousePos = (-(ScreenWidth/2-mouseX)/SCALE, -(ScreenHeight/2-mouseY)/SCALE)
		# print(mousePos)
		try:
			lastSegments = segments.copy()
			# 갱신 필요
			mousePos = (-(ScreenWidth/2-mouseX)/SCALE, (ScreenHeight/2-mouseY)/SCALE)
			# segments = []
			# for angle in range(0, 360, 20):
			# 	temp = recursive_reflect(originala, originalb, mousePos, angle, 100, SCALE)
			# 	for x in temp:
			# 		segments.append(x)
			segments = recursive_reflect(originala, originalb, mousePos, 45, 360, SCALE)
		except:
			segments = lastSegments
			pass