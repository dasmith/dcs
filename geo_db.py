
# read in geobase
# ftp://ftp.cs.utexas.edu/pub/mooney/nl-ilp-data/geosystem/geobase

_state = []
_population = {}
_major = [] # major cities
_area = {}
_capital = {}
_contains= {}
_state_abbr = {}
_city = []


def state():
    return [(s,) for s in _state]

def major():
    return [(c,) for c in _major]

def population():
    return _population.items()

def area():
    return _area.items()

def captial():
    return _capital.items()

def city():
    return [(c,) for c in _city]

def contains():
    return _contains.items()

loc = contains

def add_state(line):
    line = line.replace("'","")
    name, abbr, capital, population, area,\
            number, city1, city2, city3, city4 = line[6:-2].split(",")
    _state.append(abbr) 
    _state_abbr[name] = abbr
    _population[abbr] = population

    _area[abbr] = area 
    _capital[abbr] = area 

def add_city(line):
    line = line.replace("'","")
    state, stateabbr, city, population = line[5:-2].split(",")
    _city.append(city)
    population = int(population)
    if population > 500000:
        _major.append(city)
    _population[city] = population
    _contains[city] = stateabbr 

def add_border(line):
    pass

with open('geobase', 'r') as f:
    for line in f:
        if line.endswith(".\n"):
            if line.startswith("state"): 
                add_state(line.strip())
            elif line.startswith("city"): 
                add_city(line.strip())
            elif line.startswith("border"): 
                add_border(line.strip())

if __name__ == '__main__':
    print len(_city), len(_major)
if False:
    print population()
    print captial()
    print contains()
