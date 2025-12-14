# GenerateBlocks Query Loop Patterns

## Basic Post Grid

```html
<!-- wp:generateblocks/query-loop {"uniqueId":"1ef4ae52","postType":"post","postsPerPage":6,"columns":3,"columnsTablet":2,"columnsMobile":1,"horizontalGap":"30px","verticalGap":"30px"} -->
<div class="gb-query-loop gb-query-loop-1ef4ae52">

    <!-- wp:generateblocks/loop-item {"uniqueId":"679dacf6"} -->
    <article class="gb-loop-item">

        <!-- Featured Image -->
        <!-- wp:generateblocks/image {"uniqueId":"f75ff602","useDynamicData":true,"dynamicContentType":"featured-image","sizeSlug":"medium_large"} -->
        <figure class="gb-image gb-image-f75ff602">
            {{featured_image}}
        </figure>
        <!-- /wp:generateblocks/image -->

        <!-- Content Container -->
        <!-- wp:generateblocks/container {"uniqueId":"79cc43cc","paddingTop":"20px"} -->
        <div class="gb-container">

            <!-- Category -->
            <!-- wp:generateblocks/headline {"uniqueId":"e0405f38","element":"span","fontSize":"12px","textTransform":"uppercase","dynamicContentType":"post-terms","termSource":"category"} -->
            <span class="gb-headline">{{post_terms source="category"}}</span>
            <!-- /wp:generateblocks/headline -->

            <!-- Title -->
            <!-- wp:generateblocks/headline {"uniqueId":"c692d0e3","element":"h3","dynamicContentType":"post-title","dynamicLinkType":"post-url"} -->
            <h3 class="gb-headline"><a href="{{post_url}}">{{post_title}}</a></h3>
            <!-- /wp:generateblocks/headline -->

            <!-- Excerpt -->
            <!-- wp:generateblocks/headline {"uniqueId":"9f162737","element":"p","dynamicContentType":"post-excerpt"} -->
            <p class="gb-headline">{{post_excerpt}}</p>
            <!-- /wp:generateblocks/headline -->

            <!-- Meta -->
            <!-- wp:generateblocks/container {"uniqueId":"26b7c179","isGrid":true,"alignItems":"center","columnGap":"10px"} -->
            <div class="gb-container">
                <!-- wp:generateblocks/headline {"uniqueId":"cd057874","element":"span","fontSize":"14px","dynamicContentType":"post-date"} -->
                <span class="gb-headline">{{post_date}}</span>
                <!-- /wp:generateblocks/headline -->
                <!-- wp:generateblocks/headline {"uniqueId":"76b6724a","element":"span","fontSize":"14px","dynamicContentType":"post-author"} -->
                <span class="gb-headline">by {{post_author}}</span>
                <!-- /wp:generateblocks/headline -->
            </div>
            <!-- /wp:generateblocks/container -->

        </div>
        <!-- /wp:generateblocks/container -->

    </article>
    <!-- /wp:generateblocks/loop-item -->

</div>
<!-- /wp:generateblocks/query-loop -->
```

## Featured Posts Slider

```html
<!-- wp:generateblocks/query-loop {"uniqueId":"ade8f757","postType":"post","postsPerPage":5,"stickyPosts":"only","columns":1} -->
<div class="gb-query-loop gb-query-loop-ade8f757">

    <!-- wp:generateblocks/loop-item {"uniqueId":"d836bfa6"} -->
    <div class="gb-loop-item slide">

        <!-- Background Image Container -->
        <!-- wp:generateblocks/container {"uniqueId":"95af1c53","minHeight":"500px","minHeightMobile":"300px","verticalAlignment":"flex-end","bgImageDynamic":true,"paddingTop":"60px","paddingBottom":"60px","paddingLeft":"40px","paddingRight":"40px"} -->
        <div class="gb-container">

            <!-- Overlay -->
            <!-- wp:generateblocks/container {"uniqueId":"0c99aa1c","backgroundColor":"rgba(0,0,0,0.5)","position":"absolute","top":"0","left":"0","width":"100%","height":"100%"} -->
            <div class="gb-container"></div>
            <!-- /wp:generateblocks/container -->

            <!-- Content -->
            <!-- wp:generateblocks/container {"uniqueId":"5364798d","width":"600px","widthMobile":"100%","position":"relative","zIndex":"1"} -->
            <div class="gb-container">

                <!-- wp:generateblocks/headline {"uniqueId":"b53f80d2","element":"h2","textColor":"#ffffff","fontSize":"42px","fontSizeMobile":"28px","dynamicContentType":"post-title","dynamicLinkType":"post-url"} -->
                <h2 class="gb-headline"><a href="{{post_url}}">{{post_title}}</a></h2>
                <!-- /wp:generateblocks/headline -->

                <!-- wp:generateblocks/button-container {"uniqueId":"919522ac"} -->
                <div class="gb-button-wrapper">
                    <!-- wp:generateblocks/button {"uniqueId":"f938b569","backgroundColor":"#ffffff","textColor":"#000000","dynamicLinkType":"post-url"} -->
                    <a class="gb-button" href="{{post_url}}">Read More</a>
                    <!-- /wp:generateblocks/button -->
                </div>
                <!-- /wp:generateblocks/button-container -->

            </div>
            <!-- /wp:generateblocks/container -->

        </div>
        <!-- /wp:generateblocks/container -->

    </div>
    <!-- /wp:generateblocks/loop-item -->

</div>
<!-- /wp:generateblocks/query-loop -->
```

## Team Members Grid

```html
<!-- wp:generateblocks/query-loop {"uniqueId":"ec8916b6","postType":"team_member","postsPerPage":-1,"columns":4,"columnsTablet":2,"columnsMobile":1,"horizontalGap":"30px","verticalGap":"40px"} -->
<div class="gb-query-loop gb-query-loop-ec8916b6">

    <!-- wp:generateblocks/loop-item {"uniqueId":"a00e6ed2"} -->
    <div class="gb-loop-item">

        <!-- Photo -->
        <!-- wp:generateblocks/image {"uniqueId":"de3a86c0","useDynamicData":true,"dynamicContentType":"featured-image","borderRadius":"50%","width":"200px","height":"200px","objectFit":"cover","marginLeft":"auto","marginRight":"auto"} -->
        <figure class="gb-image">{{featured_image}}</figure>
        <!-- /wp:generateblocks/image -->

        <!-- Name -->
        <!-- wp:generateblocks/headline {"uniqueId":"f48f5c80","element":"h3","textAlign":"center","marginTop":"20px","marginBottom":"5px","dynamicContentType":"post-title"} -->
        <h3 class="gb-headline">{{post_title}}</h3>
        <!-- /wp:generateblocks/headline -->

        <!-- Position (ACF Field) -->
        <!-- wp:generateblocks/headline {"uniqueId":"9afb010e","element":"p","textAlign":"center","textColor":"#666666","fontSize":"14px","textTransform":"uppercase","letterSpacing":"1px","dynamicContentType":"acf","acfField":"position"} -->
        <p class="gb-headline">{{acf field="position"}}</p>
        <!-- /wp:generateblocks/headline -->

        <!-- Bio -->
        <!-- wp:generateblocks/headline {"uniqueId":"3e8b71a4","element":"p","textAlign":"center","marginTop":"15px","dynamicContentType":"post-excerpt"} -->
        <p class="gb-headline">{{post_excerpt}}</p>
        <!-- /wp:generateblocks/headline -->

        <!-- Social Links -->
        <!-- wp:generateblocks/container {"uniqueId":"7c4f92d1","isGrid":true,"justifyContent":"center","columnGap":"15px","marginTop":"15px"} -->
        <div class="gb-container social-links">
            <!-- Social icons here -->
        </div>
        <!-- /wp:generateblocks/container -->

    </div>
    <!-- /wp:generateblocks/loop-item -->

</div>
<!-- /wp:generateblocks/query-loop -->
```

## Product Showcase (WooCommerce)

```html
<!-- wp:generateblocks/query-loop {"uniqueId":"5d2a8e63","postType":"product","postsPerPage":8,"columns":4,"columnsTablet":2,"columnsMobile":2,"horizontalGap":"20px","verticalGap":"30px","taxQuery":[{"taxonomy":"product_cat","terms":["featured"],"field":"slug"}]} -->
<div class="gb-query-loop gb-query-loop-5d2a8e63">

    <!-- wp:generateblocks/loop-item {"uniqueId":"8f1c47b9"} -->
    <div class="gb-loop-item">

        <!-- Product Image -->
        <!-- wp:generateblocks/container {"uniqueId":"2a6d5e0f","position":"relative","overflow":"hidden"} -->
        <div class="gb-container">
            <!-- wp:generateblocks/image {"uniqueId":"c3b8f126","useDynamicData":true,"dynamicContentType":"featured-image","dynamicLinkType":"post-url"} -->
            <figure class="gb-image">
                <a href="{{post_url}}">{{featured_image}}</a>
            </figure>
            <!-- /wp:generateblocks/image -->

            <!-- Sale Badge -->
            <!-- wp:generateblocks/container {"uniqueId":"9e7d4a83","position":"absolute","top":"10px","right":"10px","backgroundColor":"#e74c3c","paddingTop":"5px","paddingRight":"10px","paddingBottom":"5px","paddingLeft":"10px","borderRadius":"3px"} -->
            <div class="gb-container">
                <!-- wp:generateblocks/headline {"uniqueId":"6b2f9c51","element":"span","textColor":"#ffffff","fontSize":"12px","fontWeight":"bold"} -->
                <span class="gb-headline">SALE</span>
                <!-- /wp:generateblocks/headline -->
            </div>
            <!-- /wp:generateblocks/container -->
        </div>
        <!-- /wp:generateblocks/container -->

        <!-- Product Info -->
        <!-- wp:generateblocks/container {"uniqueId":"d4e1a7f8","paddingTop":"15px"} -->
        <div class="gb-container">

            <!-- Category -->
            <!-- wp:generateblocks/headline {"uniqueId":"1f5c8b92","element":"span","fontSize":"12px","textColor":"#888888","dynamicContentType":"post-terms","termSource":"product_cat"} -->
            <span class="gb-headline">{{post_terms source="product_cat"}}</span>
            <!-- /wp:generateblocks/headline -->

            <!-- Title -->
            <!-- wp:generateblocks/headline {"uniqueId":"a8d3e6c4","element":"h3","fontSize":"16px","marginTop":"5px","marginBottom":"10px","dynamicContentType":"post-title","dynamicLinkType":"post-url"} -->
            <h3 class="gb-headline"><a href="{{post_url}}">{{post_title}}</a></h3>
            <!-- /wp:generateblocks/headline -->

            <!-- Price (Custom Field) -->
            <!-- wp:generateblocks/headline {"uniqueId":"7e9b2f15","element":"span","fontSize":"18px","fontWeight":"bold","textColor":"#333333","dynamicContentType":"post-meta","metaKey":"_price"} -->
            <span class="gb-headline">${{post_meta meta_key="_price"}}</span>
            <!-- /wp:generateblocks/headline -->

        </div>
        <!-- /wp:generateblocks/container -->

    </div>
    <!-- /wp:generateblocks/loop-item -->

</div>
<!-- /wp:generateblocks/query-loop -->
```

## Related Posts

```html
<!-- wp:generateblocks/query-loop {"uniqueId":"4c8a1d67","postType":"post","postsPerPage":3,"excludeCurrent":true,"columns":3,"columnsTablet":2,"columnsMobile":1,"horizontalGap":"30px","taxQueryRelation":"category"} -->
<div class="gb-query-loop gb-query-loop-4c8a1d67">

    <!-- Section Title -->
    <!-- wp:generateblocks/headline {"uniqueId":"b5f2e9a3","element":"h2","marginBottom":"30px"} -->
    <h2 class="gb-headline">Related Posts</h2>
    <!-- /wp:generateblocks/headline -->

    <!-- wp:generateblocks/loop-item {"uniqueId":"e6d4c8b1"} -->
    <article class="gb-loop-item">

        <!-- wp:generateblocks/container {"uniqueId":"2f7a9e54","isGrid":true,"flexDirection":"column"} -->
        <div class="gb-container">

            <!-- wp:generateblocks/image {"uniqueId":"8c1b5d36","useDynamicData":true,"dynamicContentType":"featured-image","sizeSlug":"medium","dynamicLinkType":"post-url"} -->
            <figure class="gb-image">
                <a href="{{post_url}}">{{featured_image}}</a>
            </figure>
            <!-- /wp:generateblocks/image -->

            <!-- wp:generateblocks/headline {"uniqueId":"3a9f7c28","element":"h4","marginTop":"15px","dynamicContentType":"post-title","dynamicLinkType":"post-url"} -->
            <h4 class="gb-headline"><a href="{{post_url}}">{{post_title}}</a></h4>
            <!-- /wp:generateblocks/headline -->

            <!-- wp:generateblocks/headline {"uniqueId":"d1e6b4a9","element":"span","fontSize":"14px","textColor":"#888888","dynamicContentType":"post-date"} -->
            <span class="gb-headline">{{post_date}}</span>
            <!-- /wp:generateblocks/headline -->

        </div>
        <!-- /wp:generateblocks/container -->

    </article>
    <!-- /wp:generateblocks/loop-item -->

</div>
<!-- /wp:generateblocks/query-loop -->
```

## Testimonials Carousel

```html
<!-- wp:generateblocks/query-loop {"uniqueId":"5b3c8f91","postType":"testimonial","postsPerPage":-1,"columns":1,"className":"testimonials-carousel"} -->
<div class="gb-query-loop gb-query-loop-5b3c8f91 testimonials-carousel">

    <!-- wp:generateblocks/loop-item {"uniqueId":"a2d7e6c4"} -->
    <div class="gb-loop-item testimonial-slide">

        <!-- wp:generateblocks/container {"uniqueId":"9f4b1e87","backgroundColor":"#f9f9f9","paddingTop":"40px","paddingRight":"40px","paddingBottom":"40px","paddingLeft":"40px","borderRadius":"8px","textAlign":"center"} -->
        <div class="gb-container">

            <!-- Quote Icon -->
            <!-- wp:generateblocks/headline {"uniqueId":"6c8d2a15","element":"span","fontSize":"48px","textColor":"#0073aa","marginBottom":"20px"} -->
            <span class="gb-headline">"</span>
            <!-- /wp:generateblocks/headline -->

            <!-- Testimonial Content -->
            <!-- wp:generateblocks/headline {"uniqueId":"b7e3f492","element":"p","fontSize":"18px","lineHeight":"1.8","fontStyle":"italic","dynamicContentType":"post-content"} -->
            <p class="gb-headline">{{post_content}}</p>
            <!-- /wp:generateblocks/headline -->

            <!-- Author Info -->
            <!-- wp:generateblocks/container {"uniqueId":"1a5c9d38","isGrid":true,"justifyContent":"center","alignItems":"center","columnGap":"15px","marginTop":"30px"} -->
            <div class="gb-container">

                <!-- wp:generateblocks/image {"uniqueId":"e4f8b267","useDynamicData":true,"dynamicContentType":"featured-image","width":"60px","height":"60px","borderRadius":"50%","objectFit":"cover"} -->
                <figure class="gb-image">{{featured_image}}</figure>
                <!-- /wp:generateblocks/image -->

                <!-- wp:generateblocks/container {"uniqueId":"7d2c6a94","textAlign":"left"} -->
                <div class="gb-container">
                    <!-- wp:generateblocks/headline {"uniqueId":"3b8e1f56","element":"strong","dynamicContentType":"post-title"} -->
                    <strong class="gb-headline">{{post_title}}</strong>
                    <!-- /wp:generateblocks/headline -->
                    <!-- wp:generateblocks/headline {"uniqueId":"c9a4d7e2","element":"span","fontSize":"14px","textColor":"#666666","dynamicContentType":"acf","acfField":"role"} -->
                    <span class="gb-headline">{{acf field="role"}}</span>
                    <!-- /wp:generateblocks/headline -->
                </div>
                <!-- /wp:generateblocks/container -->

            </div>
            <!-- /wp:generateblocks/container -->

        </div>
        <!-- /wp:generateblocks/container -->

    </div>
    <!-- /wp:generateblocks/loop-item -->

</div>
<!-- /wp:generateblocks/query-loop -->
```

## Query with Pagination

```html
<!-- wp:generateblocks/query-loop {"uniqueId":"8e6f3b19","postType":"post","postsPerPage":12,"columns":3,"columnsTablet":2,"columnsMobile":1,"horizontalGap":"30px","verticalGap":"30px","pagination":true,"paginationType":"numbers"} -->
<div class="gb-query-loop gb-query-loop-8e6f3b19">

    <!-- Loop items here -->
    <!-- wp:generateblocks/loop-item {"uniqueId":"2c7d9a45"} -->
    <article class="gb-loop-item">
        <!-- Post content blocks -->
    </article>
    <!-- /wp:generateblocks/loop-item -->

    <!-- Pagination automatically added by GB Pro -->

</div>
<!-- /wp:generateblocks/query-loop -->
```

## CSS for Query Patterns

```css
/* Post Grid Hover Effects */
.gb-query-loop .gb-loop-item {
    transition: transform 0.3s ease, box-shadow 0.3s ease;
}

.gb-query-loop .gb-loop-item:hover {
    transform: translateY(-5px);
    box-shadow: 0 10px 30px rgba(0,0,0,0.1);
}

/* Testimonials Carousel */
.testimonials-carousel {
    position: relative;
    overflow: hidden;
}

.testimonials-carousel .gb-loop-item {
    opacity: 0;
    position: absolute;
    top: 0;
    left: 0;
    width: 100%;
    transition: opacity 0.5s ease;
}

.testimonials-carousel .gb-loop-item.active {
    opacity: 1;
    position: relative;
}

/* Product Grid */
.gb-query-loop-5d2a8e63 .gb-loop-item .gb-image img {
    transition: transform 0.3s ease;
}

.gb-query-loop-5d2a8e63 .gb-loop-item:hover .gb-image img {
    transform: scale(1.05);
}

/* Pagination Styling */
.gb-query-loop-pagination {
    display: flex;
    justify-content: center;
    gap: 10px;
    margin-top: 40px;
}

.gb-query-loop-pagination a {
    padding: 10px 15px;
    background: #f0f0f0;
    border-radius: 4px;
    transition: background 0.3s ease;
}

.gb-query-loop-pagination a:hover,
.gb-query-loop-pagination .current {
    background: #0073aa;
    color: #fff;
}
```
