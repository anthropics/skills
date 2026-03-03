Netmask = require('netmask').Netmask

ip = process.argv[2]
netmask = new Netmask(ip)

out = console.log
out "Address: #{ip.split('/', 1)[0]}"
out "Netmask: #{netmask.mask} = #{netmask.bitmask}"
out "Wildcard: #{netmask.hostmask}"
out "=>"
out "Network: #{netmask.base}/#{netmask.bitmask}"
out "HostMin: #{netmask.first}"
out "HostMax: #{netmask.last}"
out "Broadcast: #{netmask.broadcast}"
out "Hosts/Net: #{netmask.size}"

out netmask.next()