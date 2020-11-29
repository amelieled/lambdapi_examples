LP_SRC = $(wildcard *.lp)
LP_OBJ = $(LP_SRC:%.lp=%.lpo)

default: $(LP_OBJ)

$(LP_OBJ)&: $(LP_SRC)
	lambdapi check $^

clean:
	rm -f $(LP_OBJ)
