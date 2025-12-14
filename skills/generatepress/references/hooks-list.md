# GeneratePress Complete Hooks Reference

## Header Hooks

| Hook | Location | Priority |
|------|----------|----------|
| `generate_before_header` | Before `<header>` | 10 |
| `generate_header` | Inside header | 10 |
| `generate_before_header_content` | Start of header content | 10 |
| `generate_after_header_content` | End of header content | 10 |
| `generate_after_header` | After `</header>` | 10 |

### Site Branding Hooks

| Hook | Location |
|------|----------|
| `generate_before_logo` | Before logo/title |
| `generate_after_logo` | After logo/title |
| `generate_site_branding_inside` | Inside branding wrapper |

## Navigation Hooks

### Primary Navigation

| Hook | Location |
|------|----------|
| `generate_before_primary_navigation` | Before primary nav |
| `generate_after_primary_navigation` | After primary nav |
| `generate_inside_navigation` | Inside nav wrapper |
| `generate_navigation_before` | Before nav items |
| `generate_navigation_after` | After nav items |

### Mobile Navigation

| Hook | Location |
|------|----------|
| `generate_inside_mobile_menu` | Inside mobile menu container |
| `generate_inside_mobile_menu_bar` | Inside mobile menu bar |
| `generate_after_mobile_menu_bar` | After mobile menu bar |

### Secondary Navigation (GP Premium)

| Hook | Location |
|------|----------|
| `generate_before_secondary_navigation` | Before secondary nav |
| `generate_after_secondary_navigation` | After secondary nav |
| `generate_inside_secondary_navigation` | Inside secondary nav |

## Content Hooks

### Main Container

| Hook | Location |
|------|----------|
| `generate_before_main_content` | Before main content area |
| `generate_after_main_content` | After main content area |
| `generate_inside_container` | Inside main container |

### Loop Hooks

| Hook | Location |
|------|----------|
| `generate_before_loop` | Before loop starts |
| `generate_after_loop` | After loop ends |
| `generate_before_do_template_part` | Before template part |
| `generate_after_do_template_part` | After template part |

### Entry Hooks

| Hook | Location |
|------|----------|
| `generate_before_entry` | Before `<article>` |
| `generate_after_entry` | After `</article>` |
| `generate_inside_article` | Inside article |

### Entry Title

| Hook | Location |
|------|----------|
| `generate_before_entry_title` | Before entry title |
| `generate_after_entry_title` | After entry title |

### Entry Content

| Hook | Location |
|------|----------|
| `generate_before_content` | Before entry content |
| `generate_after_content` | After entry content |

### Featured Image

| Hook | Location |
|------|----------|
| `generate_before_featured_image` | Before featured image |
| `generate_after_featured_image` | After featured image |

### Post Meta

| Hook | Location |
|------|----------|
| `generate_before_post_meta` | Before post meta |
| `generate_after_post_meta` | After post meta |

### Archive

| Hook | Location |
|------|----------|
| `generate_before_archive_title` | Before archive title |
| `generate_after_archive_title` | After archive title |
| `generate_after_archive_description` | After archive description |

## Sidebar Hooks

### Right Sidebar

| Hook | Location |
|------|----------|
| `generate_before_right_sidebar` | Before right sidebar |
| `generate_after_right_sidebar` | After right sidebar |
| `generate_before_right_sidebar_content` | Start of sidebar content |
| `generate_after_right_sidebar_content` | End of sidebar content |

### Left Sidebar

| Hook | Location |
|------|----------|
| `generate_before_left_sidebar` | Before left sidebar |
| `generate_after_left_sidebar` | After left sidebar |
| `generate_before_left_sidebar_content` | Start of sidebar content |
| `generate_after_left_sidebar_content` | End of sidebar content |

## Footer Hooks

### Main Footer

| Hook | Location |
|------|----------|
| `generate_before_footer` | Before `<footer>` |
| `generate_after_footer` | After `</footer>` |
| `generate_before_footer_content` | Start of footer content |
| `generate_after_footer_content` | End of footer content |

### Footer Widgets

| Hook | Location |
|------|----------|
| `generate_before_footer_widgets` | Before footer widgets area |
| `generate_after_footer_widgets` | After footer widgets area |
| `generate_inside_footer_widget` | Inside each widget area |

### Footer Bar

| Hook | Location |
|------|----------|
| `generate_before_footer_bar` | Before footer bar |
| `generate_after_footer_bar` | After footer bar |
| `generate_inside_footer_bar` | Inside footer bar |

## Page Builder Hooks

| Hook | Location |
|------|----------|
| `generate_before_page_builder_content` | Before page builder |
| `generate_after_page_builder_content` | After page builder |

## Comments Hooks

| Hook | Location |
|------|----------|
| `generate_before_comments` | Before comments section |
| `generate_after_comments` | After comments section |
| `generate_before_comments_container` | Before comments container |
| `generate_after_comments_container` | After comments container |

## 404 Page Hooks

| Hook | Location |
|------|----------|
| `generate_before_404_content` | Before 404 content |
| `generate_after_404_content` | After 404 content |

## Hook Examples

### Adding Content Before Header

```php
add_action( 'generate_before_header', 'add_top_bar', 5 );
function add_top_bar() {
    ?>
    <div class="top-bar">
        <div class="inside-top-bar grid-container">
            <span class="phone"><?php esc_html_e( 'Call: 123-456-7890', 'textdomain' ); ?></span>
            <span class="email"><?php esc_html_e( 'Email: info@example.com', 'textdomain' ); ?></span>
        </div>
    </div>
    <?php
}
```

### Adding CTA After Content

```php
add_action( 'generate_after_content', 'add_post_cta' );
function add_post_cta() {
    if ( ! is_singular( 'post' ) ) {
        return;
    }
    ?>
    <div class="post-cta">
        <h3><?php esc_html_e( 'Enjoyed this post?', 'textdomain' ); ?></h3>
        <p><?php esc_html_e( 'Subscribe for more!', 'textdomain' ); ?></p>
        <?php echo do_shortcode( '[newsletter_form]' ); ?>
    </div>
    <?php
}
```

### Custom Mobile Menu Content

```php
add_action( 'generate_inside_mobile_menu', 'add_mobile_menu_extras', 15 );
function add_mobile_menu_extras() {
    ?>
    <div class="mobile-menu-extras">
        <a href="<?php echo esc_url( wc_get_cart_url() ); ?>" class="mobile-cart">
            <span class="cart-count"><?php echo WC()->cart->get_cart_contents_count(); ?></span>
            <?php esc_html_e( 'Cart', 'textdomain' ); ?>
        </a>
    </div>
    <?php
}
```

### Replace Footer Copyright

```php
add_action( 'generate_inside_footer_bar', 'custom_footer_bar' );
function custom_footer_bar() {
    ?>
    <div class="copyright-bar">
        <span class="copyright">&copy; <?php echo date( 'Y' ); ?> <?php bloginfo( 'name' ); ?></span>
        <span class="credits"><?php esc_html_e( 'Built with GeneratePress', 'textdomain' ); ?></span>
    </div>
    <?php
}

// Remove default copyright
add_action( 'init', function() {
    remove_action( 'generate_credits', 'generate_add_footer_info' );
} );
```

### Conditional Hook Content

```php
add_action( 'generate_after_entry_title', 'add_reading_time' );
function add_reading_time() {
    if ( ! is_singular( 'post' ) ) {
        return;
    }

    $content = get_post_field( 'post_content', get_the_ID() );
    $word_count = str_word_count( strip_tags( $content ) );
    $reading_time = ceil( $word_count / 200 );

    printf(
        '<span class="reading-time">%s %s</span>',
        esc_html( $reading_time ),
        esc_html__( 'min read', 'textdomain' )
    );
}
```

## Hook Priority Guide

- `1-5`: Very early (before default content)
- `10`: Default priority
- `15-20`: After default content
- `50+`: Very late execution

```php
// Run before default header content
add_action( 'generate_header', 'my_early_header_content', 5 );

// Run after default header content
add_action( 'generate_header', 'my_late_header_content', 15 );
```
