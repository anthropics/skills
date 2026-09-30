#!/usr/bin/env python3
"""
PDF签名工具
用法: python add_pdf_signature.py <签名图片> <PDF文件> [选项]

选项:
  --position: 签名位置 (右下角/左下角/右上角/左上角, 默认: 右下角)
  --pages: 签名页面 (每页/尾页, 默认: 每页)
  --size: 签名宽度，单位点 (默认: 80)
  --output: 输出文件路径 (默认: 原文件名_已签名.pdf)
"""

import argparse
import os
import io
import sys
from PIL import Image
import numpy as np
from pypdf import PdfReader, PdfWriter
from reportlab.pdfgen import canvas


def process_signature_image(signature_path, brightness_threshold=80):
    """
    处理签名图片: 精确裁剪并去除背景
    
    Args:
        signature_path: 签名图片路径
        brightness_threshold: 亮度阈值，用于检测签名笔迹
    
    Returns:
        PIL.Image: 处理后的签名图片(RGBA格式，透明背景)
    """
    print(f"处理签名图片: {signature_path}")
    
    # 打开图片
    img = Image.open(signature_path)
    original_size = img.size
    print(f"  原始尺寸: {original_size}")
    
    # 转换为灰度图进行分析
    gray = img.convert('L')
    gray_array = np.array(gray)
    
    # 使用阈值检测签名笔迹
    dark_pixels = gray_array < brightness_threshold
    rows = np.any(dark_pixels, axis=1)
    cols = np.any(dark_pixels, axis=0)
    
    if not (rows.any() and cols.any()):
        print("  警告: 未能检测到签名区域，使用原始图片")
        img_cropped = img
    else:
        # 找到签名边界
        y_indices = np.where(rows)[0]
        x_indices = np.where(cols)[0]
        y_min, y_max = y_indices[0], y_indices[-1]
        x_min, x_max = x_indices[0], x_indices[-1]
        
        # 添加边距
        margin = 30
        y_min = max(0, y_min - margin)
        y_max = min(gray_array.shape[0], y_max + margin)
        x_min = max(0, x_min - margin)
        x_max = min(gray_array.shape[1], x_max + margin)
        
        # 裁剪
        img_cropped = img.crop((x_min, y_min, x_max, y_max))
        print(f"  裁剪后尺寸: {img_cropped.size}")
    
    # 转换为RGBA并处理背景
    img_rgba = img_cropped.convert("RGBA")
    datas = np.array(img_rgba)
    
    # 去除背景，保留签名笔迹
    for i in range(datas.shape[0]):
        for j in range(datas.shape[1]):
            r, g, b, a = datas[i, j]
            brightness = (int(r) + int(g) + int(b)) / 3
            
            if brightness > 150:  # 浅色背景 -> 透明
                datas[i, j] = [255, 255, 255, 0]
            elif brightness > 100:  # 中等亮度 -> 半透明
                alpha = int((150 - brightness) / 50 * 255)
                datas[i, j] = [r, g, b, alpha]
            else:  # 深色笔迹 -> 不透明
                datas[i, j] = [r, g, b, 255]
    
    img_final = Image.fromarray(datas, 'RGBA')
    print(f"  ✓ 签名处理完成")
    
    return img_final


def calculate_signature_position(page_width, page_height, sig_width, sig_height, position):
    """
    计算签名在页面上的位置
    
    Args:
        page_width: 页面宽度
        page_height: 页面高度
        sig_width: 签名宽度
        sig_height: 签名高度
        position: 位置选项 (右下角/左下角/右上角/左上角)
    
    Returns:
        tuple: (x, y) 坐标
    """
    margin = 40  # 边距
    
    position_map = {
        '右下角': (page_width - sig_width - margin, margin),
        '左下角': (margin, margin),
        '右上角': (page_width - sig_width - margin, page_height - sig_height - margin),
        '左上角': (margin, page_height - sig_height - margin),
    }
    
    return position_map.get(position, position_map['右下角'])


def add_signature_to_pdf(pdf_path, signature_img, output_path, position='右下角', 
                         pages='每页', signature_width=80):
    """
    在PDF上添加签名
    
    Args:
        pdf_path: PDF文件路径
        signature_img: 处理后的签名图片(PIL.Image对象)
        output_path: 输出文件路径
        position: 签名位置
        pages: 签名页面选项 (每页/尾页)
        signature_width: 签名宽度(点)
    """
    print(f"\n处理PDF: {pdf_path}")
    
    # 保存临时签名图片
    temp_sig_path = "/tmp/temp_signature.png"
    signature_img.save(temp_sig_path, "PNG")
    
    # 读取PDF
    reader = PdfReader(pdf_path)
    writer = PdfWriter()
    total_pages = len(reader.pages)
    
    print(f"  总页数: {total_pages}")
    print(f"  签名选项: {pages}")
    print(f"  签名位置: {position}")
    
    # 计算签名高度(保持宽高比)
    aspect_ratio = signature_img.size[1] / signature_img.size[0]
    signature_height = signature_width * aspect_ratio
    
    # 确定需要签名的页面
    if pages == '尾页':
        pages_to_sign = [total_pages - 1]
    else:  # 每页
        pages_to_sign = range(total_pages)
    
    # 处理每一页
    for page_num, page in enumerate(reader.pages):
        if page_num in pages_to_sign:
            print(f"  签名第 {page_num + 1} 页...")
            
            # 获取页面尺寸
            page_width = float(page.mediabox.width)
            page_height = float(page.mediabox.height)
            
            # 创建签名水印
            packet = io.BytesIO()
            can = canvas.Canvas(packet, pagesize=(page_width, page_height))
            
            # 计算签名位置
            x_pos, y_pos = calculate_signature_position(
                page_width, page_height, 
                signature_width, signature_height, 
                position
            )
            
            # 绘制签名
            can.drawImage(temp_sig_path, 
                          x_pos, y_pos,
                          width=signature_width, 
                          height=signature_height,
                          mask='auto',
                          preserveAspectRatio=True)
            can.save()
            
            # 合并到原页面
            packet.seek(0)
            signature_pdf = PdfReader(packet)
            page.merge_page(signature_pdf.pages[0])
        
        writer.add_page(page)
    
    # 保存输出文件
    with open(output_path, "wb") as output_file:
        writer.write(output_file)
    
    print(f"\n✓ 完成! 已签名 {len(pages_to_sign)} 页")
    print(f"✓ 输出文件: {output_path}")
    
    # 清理临时文件
    if os.path.exists(temp_sig_path):
        os.remove(temp_sig_path)


def main():
    parser = argparse.ArgumentParser(
        description='PDF签名工具 - 为PDF文档添加签名',
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
示例:
  # 在PDF每一页右下角添加签名
  python add_pdf_signature.py signature.jpg document.pdf
  
  # 只在尾页左下角添加签名
  python add_pdf_signature.py signature.jpg document.pdf --position 左下角 --pages 尾页
  
  # 自定义签名大小和输出文件
  python add_pdf_signature.py signature.jpg document.pdf --size 100 --output signed.pdf
        """
    )
    
    parser.add_argument('signature', help='签名图片路径')
    parser.add_argument('pdf', help='PDF文件路径')
    parser.add_argument('--position', 
                        choices=['右下角', '左下角', '右上角', '左上角'],
                        default='右下角',
                        help='签名位置 (默认: 右下角)')
    parser.add_argument('--pages',
                        choices=['每页', '尾页'],
                        default='每页',
                        help='签名页面 (默认: 每页)')
    parser.add_argument('--size',
                        type=int,
                        default=80,
                        help='签名宽度，单位点 (默认: 80)')
    parser.add_argument('--output',
                        help='输出文件路径 (默认: 原文件名_已签名.pdf)')
    
    args = parser.parse_args()
    
    # 验证输入文件
    if not os.path.exists(args.signature):
        print(f"错误: 签名图片不存在: {args.signature}")
        sys.exit(1)
    
    if not os.path.exists(args.pdf):
        print(f"错误: PDF文件不存在: {args.pdf}")
        sys.exit(1)
    
    # 确定输出路径
    if args.output:
        output_path = args.output
    else:
        pdf_dir = os.path.dirname(args.pdf)
        pdf_name = os.path.splitext(os.path.basename(args.pdf))[0]
        output_path = os.path.join(pdf_dir, f"{pdf_name}_已签名.pdf")
    
    # 处理签名图片
    signature_img = process_signature_image(args.signature)
    
    # 添加签名到PDF
    add_signature_to_pdf(
        args.pdf,
        signature_img,
        output_path,
        position=args.position,
        pages=args.pages,
        signature_width=args.size
    )


if __name__ == '__main__':
    main()
