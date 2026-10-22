from PIL import Image, ImageDraw, ImageFont, ImageFilter

def create_modern_icon(filename="app_icon.ico"):
    # Size of the canvas (high res for scaling)
    size = (512, 512)
    
    # Create a transparent image
    img = Image.new('RGBA', size, (0, 0, 0, 0))
    draw = ImageDraw.Draw(img)
    
    # --- Design: Modern Blue Rounded Square/Shield ---
    
    # 1. Draw Main Background (Blue Rounded Rectangle)
    # Google Blue color: #4285F4 -> (66, 133, 244)
    bg_color = (33, 150, 243) # Material Design Blue
    rect_coords = [20, 20, 492, 492]
    draw.rounded_rectangle(rect_coords, radius=100, fill=bg_color)
    
    # 2. Add a subtle shadow/gradient effect (optional, simple inner lighter circle)
    # This gives it a slight 3D "button" look
    highlight_coords = [40, 40, 472, 472]
    draw.rounded_rectangle(highlight_coords, radius=90, fill=None, outline=(255, 255, 255, 50), width=10)

    # --- Design: Checkmark Symbol ---
    
    # We will draw a thick white checkmark in the center
    # Coordinates for a checkmark shape
    # Points: (Start left), (Bottom middle), (Top right)
    check_color = (255, 255, 255) # White
    
    # Using a thick line approach for the checkmark
    # Left part of check
    draw.line([(130, 280), (220, 370)], fill=check_color, width=60, joint="curve")
    # Right part of check
    draw.line([(215, 370), (390, 160)], fill=check_color, width=60, joint="curve")
    
    # Rounding the ends of the lines manually by drawing circles at the tips
    # Tip 1 (Left)
    draw.ellipse([100, 250, 160, 310], fill=check_color)
    # Tip 2 (Bottom/Corner) - smoothing the join
    draw.ellipse([190, 340, 250, 400], fill=check_color)
    # Tip 3 (Right)
    draw.ellipse([360, 130, 420, 190], fill=check_color)
    
    # --- Save as ICO ---
    # We save it including all standard Windows icon sizes
    icon_sizes = [(256, 256), (128, 128), (64, 64), (48, 48), (32, 32), (16, 16)]
    img.save(filename, format='ICO', sizes=icon_sizes)
    
    print(f"Success! {filename} created.")
    print("You can now build your app with: --icon=app_icon.ico")

if __name__ == "__main__":
    try:
        create_modern_icon()
    except ImportError:
        print("Error: Pillow library not found.")
        print("Please run: pip install Pillow")