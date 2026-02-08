
import argparse
import sys
from pathlib import Path

def remove_lean_comments(code):
    
    block_comment_pattern = r'/-[\s\S]*?-/'
    code = re.sub(block_comment_pattern, '', code)

    # 2. 한 줄 주석 제거 (-- ...)
    # -- 뒤부터 줄바꿈(\n) 전까지의 내용을 삭제합니다.
    line_comment_pattern = r'--.*'
    code = re.sub(line_comment_pattern, '', code)

    # 3. 주석 제거 후 생기는 불필요한 빈 줄 정리 (선택 사항)
    # 아무것도 없는 빈 줄이 너무 많아지면 읽기 힘드므로 정리합니다.
    code = "\n".join([line for line in code.splitlines() if line.strip()])

    return code


import re
from graphviz import Digraph

def visualize_lean_dependency(input_path, output_name):
  # 파일로 input 받을경우
    # with open(file_path, 'r', encoding='utf-8') as f:
        # content = f.read()
    # content = file_path
    try:
        with open(input_path, 'r', encoding='utf-8') as f:
            raw_content = f.read()
    except FileNotFoundError:
        print(f"Error: 파일을 찾을 수 없습니다: {input_path}")
        sys.exit(1)

    content = remove_lean_comments(raw_content)

    # 1. 키워드별 색상 설정
    style_map = {
        'theorem': {'fillcolor': '#ffcccb', 'shape': 'ellipse'}, 
        'lemma': {'fillcolor': '#fff4cc', 'shape': 'ellipse'},   
        'def': {'fillcolor': '#e1f5fe', 'shape': 'box'},        
        'example': {'fillcolor': '#e1f5fe', 'shape': 'box'},
        # 'preparation': {'fillcolor': '#e8f5e9', 'shape': 'ellipse'} # 연초록
    }
    
    # 2. 선언문 추출 (키워드와 이름을 함께 추출)
    pattern = r'(theorem|lemma|def|example)\s+([^\s\(\[\{\:]+)'
    
    found_decls = re.findall(pattern, content)
    
    dot = Digraph(comment='Lean 4 Dependency Graph')
    dot.attr(rankdir='LR', overlap='false', splines='true')

    # 노드 이름 리스트 (검색용)
    decl_names = [d[1] for d in found_decls]
    

    # 의존성을 저장할 집합 (중복 방지)
    edges = set()
    # 연결이 확인된 노드들을 저장할 집합
    connected_nodes = set()

    if len(decl_names) == 1:
      connected_nodes.add(decl_names[0])

    # 3. dependency 체크
    for i, (kind, name) in enumerate(found_decls):
                
        #  텍스트 추출
        start_idx = content.find(name)
        end_idx = content.find(found_decls[i+1][1]) if i+1 < len(found_decls) else len(content)
        body_text = content[start_idx:end_idx]
        
        # 다른 노드들을 참조하고 있는지 검사
        for other_name in decl_names:
            if name == other_name:
                continue
            
            
            word_boundary_pattern = r'\b{}\b'.format(re.escape(other_name))
            if re.search(word_boundary_pattern, body_text):
                # A가 B를 사용한다면: B -> A
                edges.add((other_name, name))
                # dot.edge(other_name,name)

                connected_nodes.add(name)       # 참조하는 노드 추가
                connected_nodes.add(other_name)
    

    for kind, name in found_decls:
        if name in connected_nodes:  # 연결된 흔적이 있는 노드만 그림
            style = style_map.get(kind, {'fillcolor': 'white', 'shape': 'box'})
            dot.node(name, name, style='filled', **style)

    # 3. node 추가
    for start, end in edges:
        dot.edge(start, end)

    # 4. 저장
    dot.render(output_name, format='png', cleanup=True)
    
def main():
    parser = argparse.ArgumentParser(description="dependency_graph")
    
    # 필수 인자: 파일 경로
    parser.add_argument("input", help="leanfilepath")
    
    # 선택 인자: 출력 파일 이름
    parser.add_argument("-o", "--output", default="lean_dependency", 
                        help="outputfilename")

    args = parser.parse_args()

    # 입력 파일 존재 확인
    input_path = Path(args.input)
    if not input_path.suffix == '.lean':
        print("Warning: ")

    visualize_lean_dependency(input_path, args.output)

if __name__ == "__main__":
    main()
