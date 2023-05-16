SOURCE=map.c main.c
OBJS=map main
TARGET=map

CFLAGS = -I. -std=gnu17 -g -O0

all: $(TARGET)

cov:
	gcc $(CFLAGS) $(SOURCE) --coverage -o $(TARGET) -I. $^

$(TARGET): $(SOURCE)
	gcc $(CFLAGS) -o $@ -I. $^

run: $(TARGET)
	./$(TARGET)

run-cov: cov
	./$(TARGET)

valgrind: $(TARGET)
	valgrind ./$(TARGET)

leak:
	valgrind --leak-check=full ./$(TARGET)

gcov: cov
	./$(TARGET)
	lcov -t "$(TARGET)" -o $(TARGET).info --rc lcov_branch_coverage=1 -c -d .
	genhtml -o $(TARGET)-lcov-report --rc lcov_branch_coverage=1 $(TARGET).info

clean:
	rm -rf $(TARGET) *.gcno *.gcda *.info $(TARGET)-lcov-report

