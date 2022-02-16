# main.py
import sys

if __name__ == "__main__":

    with open('src/hog/data/hog_'+sys.argv[1]+'.lean', 'r', encoding='utf-8') as file, open('test_log_'+sys.argv[2], 'a', encoding='utf-8') as log:
        i = 0
        for line in file:
            if i == 5:
                words = line.split(' ')
                log.write(f'Num vertices: {words[3]}\n')
                break
            i+=1