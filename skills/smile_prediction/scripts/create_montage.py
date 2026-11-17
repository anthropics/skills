import argparse
from PIL import Image, ImageDraw, ImageFont, ImageOps

def safe_font(size):
    try:
        return ImageFont.truetype("/Library/Fonts/Arial.ttf", size)
    except IOError:
        return ImageFont.load_default()

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--img_orig", required=True)
    parser.add_argument("--img_generated", required=True)
    parser.add_argument("--output", required=True)
    parser.add_argument("--label", required=True)
    args = parser.parse_args()

    img_orig = Image.open(args.img_orig).convert("RGB")
    try:
        img_post = Image.open(args.img_generated).convert("RGB")
    except Exception as e:
        print(f"Error opening {args.img_generated}: {e}")
        return

    w_orig, h_orig = img_orig.size
    w_post, h_post = img_post.size

    if (w_orig, h_orig) != (w_post, h_post):
        img_orig = ImageOps.fit(img_orig, (w_post, h_post), method=Image.Resampling.LANCZOS)
        w_orig, h_orig = w_post, h_post

    font_size = max(20, int(w_orig * 0.025))
    text_pad = int(font_size * 2)

    montage_w = w_orig
    montage_h = h_orig * 2 + text_pad * 2

    montage = Image.new("RGB", (montage_w, montage_h), (255, 255, 255))
    draw = ImageDraw.Draw(montage)

    font = safe_font(font_size)

    text_pre = f"{args.label} - Pre-Op"
    text_post = f"{args.label} - Post-Op (Predicted)"

    y_offset = (text_pad - font_size) // 2

    draw.text((w_orig * 0.05, y_offset), text_pre, fill=(0, 0, 0), font=font)
    montage.paste(img_orig, (0, text_pad))

    draw.text((w_orig * 0.05, h_orig + text_pad + y_offset), text_post, fill=(0, 0, 0), font=font)
    montage.paste(img_post, (0, h_orig + text_pad * 2))

    montage.save(args.output, quality=95)
    print(f"Saved {args.output}")

if __name__ == "__main__":
    main()
