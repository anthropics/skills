import { useState, useEffect } from 'react'
import { toast } from '@/hooks/use-toast'
import { Button } from '@/components/ui/button'
import { Card, CardContent, CardHeader, CardTitle } from '@/components/ui/card'
import { Input } from '@/components/ui/input'
import { Label } from '@/components/ui/label'
import { Textarea } from '@/components/ui/textarea'
import { Table, TableBody, TableCell, TableHead, TableHeader, TableRow } from '@/components/ui/table'
import { Badge } from '@/components/ui/badge'
import { Select, SelectContent, SelectItem, SelectTrigger, SelectValue } from '@/components/ui/select'
import { Dialog, DialogContent, DialogDescription, DialogFooter, DialogHeader, DialogTitle } from '@/components/ui/dialog'
import { DropdownMenu, DropdownMenuContent, DropdownMenuItem, DropdownMenuLabel, DropdownMenuSeparator, DropdownMenuTrigger } from '@/components/ui/dropdown-menu'
import { Search, Plus, Minus, Pencil, Trash2, MoreHorizontal, ArrowUpDown, ArrowUp, ArrowDown, Package, CheckCircle, AlertTriangle, XCircle, DollarSign } from 'lucide-react'

interface Product {
  id: string
  name: string
  category: string
  price: number
  stock: number
  status: 'in_stock' | 'low_stock' | 'out_of_stock'
  description: string
  createdAt: string
}

const CATEGORIES = ['电子产品', '服装鞋帽', '食品饮料', '家居用品', '图书文具', '美妆护肤']

const STATUS_LABELS = {
  in_stock: '有货',
  low_stock: '库存紧张',
  out_of_stock: '缺货'
}

const STATUS_COLORS = {
  in_stock: 'text-emerald-600 bg-emerald-50',
  low_stock: 'text-amber-600 bg-amber-50',
  out_of_stock: 'text-red-600 bg-red-50'
}

function App() {
  const [products, setProducts] = useState<Product[]>(() => {
    const saved = localStorage.getItem('products')
    if (saved) return JSON.parse(saved)

    return [
      {
        id: '1',
        name: 'iPhone 15 Pro',
        category: '电子产品',
        price: 7999,
        stock: 50,
        status: 'in_stock',
        description: '全新一代旗舰手机，配备 A17 Pro 芯片，钛金属边框设计',
        createdAt: new Date().toISOString()
      },
      {
        id: '2',
        name: '无线蓝牙耳机',
        category: '电子产品',
        price: 299,
        stock: 8,
        status: 'low_stock',
        description: '高品质降噪耳机，40小时超长续航',
        createdAt: new Date().toISOString()
      },
      {
        id: '3',
        name: '纯棉T恤',
        category: '服装鞋帽',
        price: 89,
        stock: 0,
        status: 'out_of_stock',
        description: '100%纯棉材质，舒适透气，多色可选',
        createdAt: new Date().toISOString()
      },
      {
        id: '4',
        name: '智能手表',
        category: '电子产品',
        price: 1299,
        stock: 25,
        status: 'in_stock',
        description: '健康监测，运动追踪，智能提醒',
        createdAt: new Date().toISOString()
      },
      {
        id: '5',
        name: '有机燕麦片',
        category: '食品饮料',
        price: 45,
        stock: 100,
        status: 'in_stock',
        description: '纯天然有机燕麦，营养健康早餐首选',
        createdAt: new Date().toISOString()
      }
    ]
  })

  const [searchTerm, setSearchTerm] = useState('')
  const [selectedCategory, setSelectedCategory] = useState('all')
  const [sortField, setSortField] = useState<'name' | 'price' | 'stock' | 'createdAt'>('createdAt')
  const [sortOrder, setSortOrder] = useState<'asc' | 'desc'>('desc')
  const [dialogOpen, setDialogOpen] = useState(false)
  const [editingProduct, setEditingProduct] = useState<Product | null>(null)

  const [formData, setFormData] = useState({
    name: '',
    category: CATEGORIES[0],
    price: '',
    stock: '',
    description: ''
  })

  useEffect(() => {
    localStorage.setItem('products', JSON.stringify(products))
  }, [products])

  const getStatus = (stock: number): Product['status'] => {
    if (stock === 0) return 'out_of_stock'
    if (stock < 10) return 'low_stock'
    return 'in_stock'
  }

  const filteredProducts = products
    .filter(p => {
      const matchesSearch = p.name.toLowerCase().includes(searchTerm.toLowerCase()) ||
                          p.description.toLowerCase().includes(searchTerm.toLowerCase())
      const matchesCategory = selectedCategory === 'all' || p.category === selectedCategory
      return matchesSearch && matchesCategory
    })
    .sort((a, b) => {
      const aVal = a[sortField]
      const bVal = b[sortField]
      if (sortOrder === 'asc') return aVal > bVal ? 1 : -1
      return aVal < bVal ? 1 : -1
    })

  const stats = {
    total: products.length,
    inStock: products.filter(p => p.status === 'in_stock').length,
    lowStock: products.filter(p => p.status === 'low_stock').length,
    outOfStock: products.filter(p => p.status === 'out_of_stock').length,
    totalValue: products.reduce((sum, p) => sum + p.price * p.stock, 0)
  }

  const handleAdd = () => {
    setEditingProduct(null)
    setFormData({
      name: '',
      category: CATEGORIES[0],
      price: '',
      stock: '',
      description: ''
    })
    setDialogOpen(true)
  }

  const handleEdit = (product: Product) => {
    setEditingProduct(product)
    setFormData({
      name: product.name,
      category: product.category,
      price: product.price.toString(),
      stock: product.stock.toString(),
      description: product.description
    })
    setDialogOpen(true)
  }

  const handleDelete = (id: string) => {
    setProducts(products.filter(p => p.id !== id))
    toast({
      title: '删除成功',
      description: '商品已删除'
    })
  }

  const handleSave = () => {
    if (!formData.name || !formData.price || !formData.stock) {
      toast({
        variant: 'destructive',
        title: '表单错误',
        description: '请填写所有必填字段'
      })
      return
    }

    const price = parseFloat(formData.price)
    const stock = parseInt(formData.stock)

    if (isNaN(price) || price < 0) {
      toast({
        variant: 'destructive',
        title: '价格错误',
        description: '请输入有效的价格'
      })
      return
    }

    if (isNaN(stock) || stock < 0) {
      toast({
        variant: 'destructive',
        title: '库存错误',
        description: '请输入有效的库存数量'
      })
      return
    }

    if (editingProduct) {
      setProducts(products.map(p => {
        if (p.id === editingProduct.id) {
          return {
            ...p,
            name: formData.name,
            category: formData.category,
            price,
            stock,
            status: getStatus(stock),
            description: formData.description
          }
        }
        return p
      }))
      toast({
        title: '更新成功',
        description: '商品信息已更新'
      })
    } else {
      const newProduct: Product = {
        id: Date.now().toString(),
        name: formData.name,
        category: formData.category,
        price,
        stock,
        status: getStatus(stock),
        description: formData.description,
        createdAt: new Date().toISOString()
      }
      setProducts([...products, newProduct])
      toast({
        title: '添加成功',
        description: '新商品已添加'
      })
    }

    setDialogOpen(false)
  }

  const updateStock = (id: string, delta: number) => {
    setProducts(products.map(p => {
      if (p.id === id) {
        const newStock = Math.max(0, p.stock + delta)
        return {
          ...p,
          stock: newStock,
          status: getStatus(newStock)
        }
      }
      return p
    }))
  }

  return (
    <div className="min-h-screen bg-gradient-to-br from-slate-50 via-blue-50 to-indigo-50">
      <div className="container mx-auto px-4 py-8 max-w-7xl">
        <div className="mb-8">
          <div className="flex items-center justify-between">
            <div>
              <h1 className="text-3xl font-bold text-slate-900 mb-2">商品管理系统</h1>
              <p className="text-slate-600">高效管理您的商品库存和价格</p>
            </div>
            <Button onClick={handleAdd} size="lg" className="gap-2">
              <Plus className="w-5 h-5" />
              添加商品
            </Button>
          </div>
        </div>

        <div className="grid grid-cols-2 md:grid-cols-5 gap-4 mb-8">
          <Card>
            <CardContent className="p-4">
              <div className="flex items-center gap-3">
                <div className="w-10 h-10 rounded-lg bg-blue-100 flex items-center justify-center">
                  <Package className="w-5 h-5 text-blue-600" />
                </div>
                <div>
                  <p className="text-2xl font-bold text-slate-900">{stats.total}</p>
                  <p className="text-xs text-slate-600">商品总数</p>
                </div>
              </div>
            </CardContent>
          </Card>
          <Card>
            <CardContent className="p-4">
              <div className="flex items-center gap-3">
                <div className="w-10 h-10 rounded-lg bg-emerald-100 flex items-center justify-center">
                  <CheckCircle className="w-5 h-5 text-emerald-600" />
                </div>
                <div>
                  <p className="text-2xl font-bold text-emerald-600">{stats.inStock}</p>
                  <p className="text-xs text-slate-600">有货</p>
                </div>
              </div>
            </CardContent>
          </Card>
          <Card>
            <CardContent className="p-4">
              <div className="flex items-center gap-3">
                <div className="w-10 h-10 rounded-lg bg-amber-100 flex items-center justify-center">
                  <AlertTriangle className="w-5 h-5 text-amber-600" />
                </div>
                <div>
                  <p className="text-2xl font-bold text-amber-600">{stats.lowStock}</p>
                  <p className="text-xs text-slate-600">库存紧张</p>
                </div>
              </div>
            </CardContent>
          </Card>
          <Card>
            <CardContent className="p-4">
              <div className="flex items-center gap-3">
                <div className="w-10 h-10 rounded-lg bg-red-100 flex items-center justify-center">
                  <XCircle className="w-5 h-5 text-red-600" />
                </div>
                <div>
                  <p className="text-2xl font-bold text-red-600">{stats.outOfStock}</p>
                  <p className="text-xs text-slate-600">缺货</p>
                </div>
              </div>
            </CardContent>
          </Card>
          <Card>
            <CardContent className="p-4">
              <div className="flex items-center gap-3">
                <div className="w-10 h-10 rounded-lg bg-purple-100 flex items-center justify-center">
                  <DollarSign className="w-5 h-5 text-purple-600" />
                </div>
                <div>
                  <p className="text-2xl font-bold text-slate-900">
                    {(stats.totalValue / 10000).toFixed(1)}万
                  </p>
                  <p className="text-xs text-slate-600">库存总值</p>
                </div>
              </div>
            </CardContent>
          </Card>
        </div>

        <Card className="mb-6">
          <CardContent className="p-4">
            <div className="flex flex-col md:flex-row gap-4">
              <div className="flex-1 relative">
                <Search className="absolute left-3 top-1/2 -translate-y-1/2 w-5 h-5 text-slate-400" />
                <Input
                  placeholder="搜索商品名称或描述..."
                  value={searchTerm}
                  onChange={(e) => setSearchTerm(e.target.value)}
                  className="pl-10"
                />
              </div>
              <Select value={selectedCategory} onValueChange={setSelectedCategory}>
                <SelectTrigger className="w-full md:w-48">
                  <SelectValue />
                </SelectTrigger>
                <SelectContent>
                  <SelectItem value="all">全部分类</SelectItem>
                  {CATEGORIES.map(cat => (
                    <SelectItem key={cat} value={cat}>{cat}</SelectItem>
                  ))}
                </SelectContent>
              </Select>
              <DropdownMenu>
                <DropdownMenuTrigger asChild>
                  <Button variant="outline" className="gap-2">
                    <ArrowUpDown className="w-4 h-4" />
                    排序
                  </Button>
                </DropdownMenuTrigger>
                <DropdownMenuContent align="end">
                  <DropdownMenuLabel>排序方式</DropdownMenuLabel>
                  <DropdownMenuSeparator />
                  {[
                    { field: 'name', label: '名称' },
                    { field: 'price', label: '价格' },
                    { field: 'stock', label: '库存' },
                    { field: 'createdAt', label: '创建时间' }
                  ].map(({ field, label }) => (
                    <DropdownMenuItem
                      key={field}
                      onClick={() => {
                        if (sortField === field) {
                          setSortOrder(sortOrder === 'asc' ? 'desc' : 'asc')
                        } else {
                          setSortField(field as any)
                          setSortOrder('asc')
                        }
                      }}
                      className={sortField === field ? 'bg-slate-100' : ''}
                    >
                      {label}
                      {sortField === field && (
                        sortOrder === 'asc' ? <ArrowUp className="w-4 h-4 ml-auto" /> : <ArrowDown className="w-4 h-4 ml-auto" />
                      )}
                    </DropdownMenuItem>
                  ))}
                </DropdownMenuContent>
              </DropdownMenu>
            </div>
          </CardContent>
        </Card>

        <Card>
          <CardHeader>
            <CardTitle>商品列表 ({filteredProducts.length})</CardTitle>
          </CardHeader>
          <CardContent>
            <Table>
              <TableHeader>
                <TableRow>
                  <TableHead>商品名称</TableHead>
                  <TableHead>分类</TableHead>
                  <TableHead>价格</TableHead>
                  <TableHead>库存</TableHead>
                  <TableHead>状态</TableHead>
                  <TableHead>操作</TableHead>
                </TableRow>
              </TableHeader>
              <TableBody>
                {filteredProducts.length === 0 ? (
                  <TableRow>
                    <TableCell colSpan={6} className="text-center text-slate-500 py-12">
                      暂无商品
                    </TableCell>
                  </TableRow>
                ) : filteredProducts.map(product => (
                  <TableRow key={product.id}>
                    <TableCell>
                      <div>
                        <p className="font-medium">{product.name}</p>
                        <p className="text-xs text-slate-500 truncate max-w-48">{product.description}</p>
                      </div>
                    </TableCell>
                    <TableCell>
                      <Badge variant="outline">{product.category}</Badge>
                    </TableCell>
                    <TableCell className="font-medium">
                      ¥{product.price.toLocaleString()}
                    </TableCell>
                    <TableCell>
                      <div className="flex items-center gap-2">
                        <Button
                          variant="ghost"
                          size="sm"
                          className="h-7 w-7 p-0"
                          onClick={() => updateStock(product.id, -1)}
                          disabled={product.stock === 0}
                        >
                          <Minus className="w-3 h-3" />
                        </Button>
                        <span className="w-8 text-center font-medium">{product.stock}</span>
                        <Button
                          variant="ghost"
                          size="sm"
                          className="h-7 w-7 p-0"
                          onClick={() => updateStock(product.id, 1)}
                        >
                          <Plus className="w-3 h-3" />
                        </Button>
                      </div>
                    </TableCell>
                    <TableCell>
                      <Badge className={STATUS_COLORS[product.status]}>
                        {STATUS_LABELS[product.status]}
                      </Badge>
                    </TableCell>
                    <TableCell>
                      <div className="flex items-center gap-1">
                        <Button
                          variant="ghost"
                          size="sm"
                          onClick={() => handleEdit(product)}
                        >
                          <Pencil className="w-4 h-4" />
                        </Button>
                        <DropdownMenu>
                          <DropdownMenuTrigger asChild>
                            <Button variant="ghost" size="sm">
                              <MoreHorizontal className="w-4 h-4" />
                            </Button>
                          </DropdownMenuTrigger>
                          <DropdownMenuContent align="end">
                            <DropdownMenuItem onClick={() => handleEdit(product)}>
                              <Pencil className="w-4 h-4 mr-2" />
                              编辑
                            </DropdownMenuItem>
                            <DropdownMenuItem
                              onClick={() => handleDelete(product.id)}
                              className="text-red-600"
                            >
                              <Trash2 className="w-4 h-4 mr-2" />
                              删除
                            </DropdownMenuItem>
                          </DropdownMenuContent>
                        </DropdownMenu>
                      </div>
                    </TableCell>
                  </TableRow>
                ))}
              </TableBody>
            </Table>
          </CardContent>
        </Card>
      </div>

      <Dialog open={dialogOpen} onOpenChange={setDialogOpen}>
        <DialogContent className="sm:max-w-md">
          <DialogHeader>
            <DialogTitle>{editingProduct ? '编辑商品' : '添加商品'}</DialogTitle>
            <DialogDescription>
              {editingProduct ? '修改商品信息' : '填写新商品信息'}
            </DialogDescription>
          </DialogHeader>
          <div className="space-y-4 py-4">
            <div className="space-y-2">
              <Label>商品名称 *</Label>
              <Input
                value={formData.name}
                onChange={(e) => setFormData({ ...formData, name: e.target.value })}
                placeholder="请输入商品名称"
              />
            </div>
            <div className="space-y-2">
              <Label>分类 *</Label>
              <Select
                value={formData.category}
                onValueChange={(value) => setFormData({ ...formData, category: value })}
              >
                <SelectTrigger>
                  <SelectValue />
                </SelectTrigger>
                <SelectContent>
                  {CATEGORIES.map(cat => (
                    <SelectItem key={cat} value={cat}>{cat}</SelectItem>
                  ))}
                </SelectContent>
              </Select>
            </div>
            <div className="grid grid-cols-2 gap-4">
              <div className="space-y-2">
                <Label>价格 *</Label>
                <Input
                  type="number"
                  step="0.01"
                  min="0"
                  value={formData.price}
                  onChange={(e) => setFormData({ ...formData, price: e.target.value })}
                  placeholder="0.00"
                />
              </div>
              <div className="space-y-2">
                <Label>库存 *</Label>
                <Input
                  type="number"
                  min="0"
                  value={formData.stock}
                  onChange={(e) => setFormData({ ...formData, stock: e.target.value })}
                  placeholder="0"
                />
              </div>
            </div>
            <div className="space-y-2">
              <Label>商品描述</Label>
              <Textarea
                value={formData.description}
                onChange={(e) => setFormData({ ...formData, description: e.target.value })}
                placeholder="请输入商品描述"
                rows={3}
              />
            </div>
          </div>
          <DialogFooter>
            <Button variant="outline" onClick={() => setDialogOpen(false)}>
              取消
            </Button>
            <Button onClick={handleSave}>
              {editingProduct ? '保存' : '添加'}
            </Button>
          </DialogFooter>
        </DialogContent>
      </Dialog>
    </div>
  )
}

export default App
