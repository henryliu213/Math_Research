### A Pluto.jl notebook ###
# v0.19.36

using Markdown
using InteractiveUtils

# ╔═╡ bcf7a41e-6f58-45d5-8224-f9f286a56326
using LaTeXStrings

# ╔═╡ dc894286-35b1-4f94-9774-3dd91bf6afa7
mutable struct term
	a :: Float64
	x :: Int
	xi :: Int
end


# ╔═╡ 9114e4a8-b3da-4d56-b75f-271c2597a009
function tp( a :: term)
	if a == nothing
		return 
	end
	i = a.a
	b = a.x
	c = a.xi
	if i == 0 
		return
	end
	if b ==0 && c == 0
		return
	end
	if b!= 0 && c!= 0
		if i != 1.0
			L"$%$i x^{%$b} \xi^{%$c}$"
		else
			L"$x^{%$b} \xi^{%$c}$"
		end
	elseif b == 0
		if i != 1.0
			L"$%$i  \xi^{%$c}$"
		else
			L"$ \xi^{%$c}$"
		end

	else 
		if i != 1.0
			L"$%$i x^{%$b} $"
		else
			L"$x^{%$b} $"
		end
	end
end

# ╔═╡ 5db2345c-af04-4385-83ad-6fa72af2151a
function Poly(b)
	i = 1
	string = L"This polynomial: "
	while i <= length(b)
		if !isnothing(b[i])	
			string = latexstring(string, L"", tp(b[i]))
			i = i+1
		end
	end
	return string
end

# ╔═╡ 5e14048a-bdd6-430e-b4c2-70c429e81a90
function mergeTerms(arr, x, xi)
	i = 1
	sum = 0
	result = Vector{term}()
	while i <= length(arr)
		current = arr[i]
		if current.x == x && current.xi == xi
			sum+=current.a
		else
			push!(result, current)
		end
		i+=1
	end
	
	if sum != 0
		push!(result, term(sum,x,xi))
	end
	result
	return result
end

# ╔═╡ 8a56d05e-b1b1-4f7f-90e7-ea5aa4044db8
function simplify(arr)
	D = Dict()
	i = 1
	while i <= length(arr)
		term = arr[i]
		i+=1
		if term.a == 0
			continue
		end
			if haskey(D, [term.x,term.xi])
				D[[term.x,term.xi]] += 1
			else
				D[[term.x,term.xi]] = 1
			end
	end
	for key in keys(D)
		if D[key] > 1
			arr = mergeTerms(arr, key[1], key[2])
		end
	end
	return arr 
end

# ╔═╡ 9953a8fb-2164-431e-9c3c-fde485f81a4e
function Xp(arr, a, x,xi, b, x2,xi2)
	L"$%$a x^{%$x}\xi^{%$xi}\partial x -%$b x^{%$x2}\xi^{xi2}\partial \xi$"
	if length(arr) == 0
		return
	end
	i = 1 
	result = []
	#partial x term 
	if a != 0
		while i <= length(arr)
			current = arr[i]
			i=i+1
			if current.x ==0
				continue
			end
			push!(result, term(current.a * a * current.x, x+current.x-1, xi+current.xi ))
		end
	end
	#partial xi 
	if b != 0
		i = 1
		while i <= length(arr)
			current = arr[i]
			i=i+1
			if current.xi == 0
				continue
			end
			push!(result, term(current.a * b * -1 * current.xi, x2+current.x, xi2+current.xi-1 ))
		end
	end
	result = simplify(result)
	return result
end

# ╔═╡ fdda6554-6276-43e6-91ea-87ee30af096d
function add(arr1,arr2)
	result = []
	i = 1
	while i <= length(arr1)
		push!(result, arr1[i])
		i+=1
	end
	j = 1
	while j <= length(arr2)
		push!(result, arr2[j])
		j+=1
	end
	return simplify(result)
end

# ╔═╡ 9f1cd2e0-e2bb-4ad4-b947-84c065d0c384
struct Xtrans
	a
	x
	xi
	b
	x2
	xi2
end

# ╔═╡ fab98343-ae5a-4cbb-8e1b-0654caadb05f
function Xp(arr, X :: Xtrans)
	if length(arr) == 0
		return 
	end
	return Xp(arr, X.a,X.x,X.xi,X.b,X.x2,X.xi2)
end

# ╔═╡ b1efab7d-0c4d-484f-a90d-970bb47998fb
function partialX(arr, termy)
	if length(arr) == 0
			return
	end
	i = 1 
	result = []
	#partial x term 
	if termy.a != 0
		while i <= length(arr)
			current = arr[i]
			i=i+1
			if current.x ==0
				continue
			end
			push!(result, term(current.a * termy.a * current.x, termy.x+current.x-1, termy.xi+current.xi ))
		end
	end
	result = simplify(result)
	return result;
end

# ╔═╡ 8ac44a5b-f1f3-47d7-bdbc-3896e5022400
function partialXi(arr, termy)
	if length(arr) == 0
			return
	end
	i = 1 
	result = []
	#partial xi term with built in negative
	if termy.a != 0
		while i <= length(arr)
			current = arr[i]
			i=i+1

			if current.xi ==0
				continue
			end
			push!(result, term(current.a * termy.a * current.xi * -1, termy.x+current.x, termy.xi+current.xi -1 ))
		end
	end
	result = simplify(result)
	return result;
end

# ╔═╡ 812d45ec-7b0f-449d-98c6-c1f29d7c7f47
function FullXp(arr, xs, xis)
	if length(arr) == 0 
		return []
	end
	result = []
	if length(xs)!= 0
		i = 1
		while i <= length(xs)
			currterm = xs[i]
			i+=1
			result = add(result, partialX(arr, currterm))
			
		end
	end
	if length(xis)!= 0
		i = 1
		while i <= length(xis)
			currterm = xis[i]
			i+=1 
			result = add(result, partialXi(arr, currterm ))

		end
	end
	return result
end

# ╔═╡ b1e9a030-e15a-47ff-b053-9b716cf5f7b6
function Taylor(arr, xs, xis, n) 
	if n <0
		throw(DomainError())
	end
	storeHere = copy(arr)
	prev = copy(arr)
	i = 1
	while i <= n
		print("currently calculating n = $(i) of the taylor expansion \n")
		p = length(prev)
		if p == 0 
			i+=1
			continue
		end
		print("\n\n\n\nThe previous term has $p terms\n")
		print("Previous is :: \n", Poly(prev))
		print("\n")
		prev = FullXp(prev, xs,xis)
		print("after the XP is applied, it is:\n", Poly(prev))


      #=
		fixZero = []
		k = 1
		while k<= length(prev)
			current = prev[k]
			k+=1
			if abs(current.a) <= 1/(10^15) 
				continue
			end
			push!(fixZero, term(current.a, current.x, current.xi))
			
		end
		
		prev = fixZero
 #    =#		
		
		temp = []
		j = 1
		while j <= length(prev)
			thisterm = term(prev[j].a, prev[j].x, prev[j].xi)
			thisterm.a = thisterm.a/factorial(big(i))
			push!(temp, thisterm)
			j+= 1
		end
		storeHere = add(storeHere, temp)
		#print("Store here holds\n", Poly(storeHere))
		i+= 1 
	end
	return storeHere
end


# ╔═╡ a15557b3-49d7-4690-b6c9-69630272e828
function findP(arr, degree)
	result = []
	if length(arr) == 0
		return result 
	end
	i = 1
	while i <= length(arr)
		current = arr[i]
		i+=1
		if current.xi == degree && current.xi == 2
			continue
		end
		if current.x == degree
			continue
		end
		if current.x+current.xi == degree
			coef = current.a/2/(current.x+1)
			push!(result, term(coef, current.x+1, current.xi-1))
		end
	end
	return result
end


# ╔═╡ a4395194-877f-4aad-bde2-d92a09616dbb
function findXp(arr)
	x = []
	xi = []
	if length(arr) == 0
		return x,xi
	end
	i = 1
	while i<= length(arr)
		current = arr[i]
		i+=1
		#Finding P_x
		if current.x >= 1
			push!(x, term(current.a*current.x, current.x-1, current.xi))
		end
		#Finding P_xi 
		if current.xi>= 1
			push!(xi, term(current.a*current.xi, current.x, current.xi-1))
		end
	end
	print("P_xi is ", Poly(xi))
	print("P_x is ", Poly(x))
	return x, xi 

end

# ╔═╡ 11e415ae-3a88-4f5a-81d1-8da8c0c41048
function crankThat(arr, degree, n)
	#input the H function, degree to crank out, n taylor expansion  
	myP = findP(arr,degree)
	Xp = findXp(myP)
	xs = Xp[2] #Bad notation, Xs needs P_xi, so second return in findXp
	xis = Xp[1] #Xis uses P_x
	print("\nCranking through degree $degree\n")
	FinalArray = Taylor(arr, xs, xis, n)
	return FinalArray
end


# ╔═╡ 8240db49-5fa2-4dcb-b808-30878c3dc1c5
function youPick2n(arr, degree, n)
	#input function H, the degree of the x^2n, n = number of iterations you want for each taylor expansion 
	
	i = 2
	holder = crankThat(arr,i,n)
	i+=1
	while i<= degree
		holder = crankThat(holder,i,n)
		i+=1
	end
	return holder
end

# ╔═╡ cb2c203d-abd9-4eed-b9f3-2c645e14a171
function lastnterms(arr,n)
	holder = []
	len = length(arr)
	while n>0
		push!(holder, arr[len-n+1])
		n-=1
	end	
	return holder
end

# ╔═╡ 5855996d-676d-4c23-8522-dcbe550bd278
function directCoef(termy,n,a,q,r)
	x = termy.x
	xi = termy.xi
	i = 0
	result = termy.a
	while i < n
		result = result * ((a*(r-1)*(x)-a*(q+1)*(xi))/(2*(q+1)))	
		x += q
		xi = (xi + r - 2)
		i+=1
	end
	result = result/(factorial( big(n)))
	return term(result, x, xi)
end


# ╔═╡ 78b1d53b-b859-4cf7-96d9-97c6f5510909
function directCoefCTerms(termy, n, a, q, r)
	x = termy.x
	xi = termy.xi
	i = 0
	result = termy.a
	while i < n
		result = result * ((a*(r-1)*(x)-a*(q+1)*(xi))/(2*(q+1)))	
		x += q
		xi = (xi + r - 2)
		i+=1
		result = result/i
	end
	return term(result, x, xi)

	
end

# ╔═╡ dff3fbb3-5510-4fd1-82a7-8e540b8e73d3
function DCTaylor(arr, crankTermy, n)  
	result = []
	for termy in arr
		a = crankTermy.a
		q = crankTermy.x
		r = crankTermy.xi 
		i = 0
		newA = termy.a
		x = termy.x
		xi = termy.xi
		while i < n 
			newA = newA * ((a*(r-1)*(x)-a*(q+1)*(xi))/(2*(q+1)))
			x+= q
			xi += (r-2)
			i+=1
			newA = newA/i
			push!(result, term(newA,x,xi))
		end
	end
	
	if length(result) == 0 
		print("Lenght resutlt was 0")
		return arr
	end
	final = add(arr,result)
	final = sort(final, by=x->x.x+x.xi)
	return final
end


# ╔═╡ b03b364e-3c7f-46aa-b6b7-7b4eb16e1412
function DCcrankThat(arr, degree, n) #Assuming you can do one at a time
	allTermsofThisDegree = []
	for termy in arr
		if termy.xi == 2 && degree == 2
			continue
		end
		if termy.x == degree 
			continue
		end
		if termy.x + termy.xi == degree && termy.x < degree 
			push!(allTermsofThisDegree, termy)
		end
	end
	FinalArray = arr
	for CrankTermy in allTermsofThisDegree
		FinalArray = DCTaylor(FinalArray, CrankTermy, n)
	end
	if length(FinalArray) == 0
		return filter((x)-> !isnothing(x) && x.a != 0 , Arr)
	else 
		return filter((x)-> !isnothing(x), FinalArray)
	end
end


# ╔═╡ 89ffed51-2842-46d7-96b7-e67ba44a6eec
function DCpickdegree(arr, degree, n)
	if degree == 0
		return arr
	end
	i = 1
	holder = DCcrankThat(arr,i,n)
	i+=1
	while i<= degree
		holder = DCcrankThat(holder,i,n)
		i+=1
	end
	holder = filter((x)-> !isnothing(x) && x.a != 0, holder)
	return sort(holder, by = x->x.x+x.xi)
end

# ╔═╡ c342c6f1-5737-4617-9341-332ed6cfcdef
function Main()
	# Build your terms here, term(coeficient, x degree, xi degree)
	A = term(1,0,2)
	B = term(1,10,0)
	C = term(2.3,13,2)
	D = term(0.001,2,4)
	E  = term(0.001,1,5)
	#assemble it into an array 
	arr = [A,B,C]
	
	#input your function(array, degree you want to push past, number of taylor expansions terms)
	
	#Poly(arr)
	p = youPick2n(arr, 15, 3)
	lastnterms(p, 90)
	#Poly(p)    #this function hurts the computer but shows everything 
	#Poly(arr)

end


# ╔═╡ bd799c26-57c6-4fb7-906c-ef200c047638
#Main()  # Old function, printing last terms 

# ╔═╡ 4ca3155f-93cb-45d1-b2d1-1db3f1ed611c
function Main2()
	# Build your terms here, term(coeficient, x degree, xi degree)
	C = term(1,0,2)
	A = term(1,4,0)
	B = term(4,3,6)
	D = term(4,2,7)
	E  = term(0.001,70,3)
	#assemble it into an array 
	arr = [C,A,B,D]
	DegreeofB = B.x+B.xi
	#input your function(array, degree you want to push past, number of taylor expansions terms)
	
	#Poly(arr)
	p = youPick2n(arr, DegreeofB, 4 )
	#a = directCoefCTerms(C, 3, 4, 3, 6)

	Poly(p)    #this function hurts the computer but shows everything 
	#lastnterms(p, 10)

	#Poly([a]) #A term is the x^2n 
	
end


# ╔═╡ 902fe444-12cb-4405-96fb-b839c70ea0f2
# ╠═╡ show_logs = false
#Main2() #Old function to test with new function 

# ╔═╡ cb236f21-a215-468d-b05c-8b0cc11bfd83
function bound(q,r)
	if (r-1)*q-(q+1)*(r-2)==0
		return 9999999
	end
	
	bound = abs(2(q+1)/((r-1)*q-(q+1)*(r-2)))
	return bound
end


# ╔═╡ f22cde20-e89c-4e09-b19d-75235d59983d
function Main5()
	# Build your terms here, term(coeficient, x degree, xi degree)
	C = term(1,0,2)
	A = term(2,1,1)
	B = term(1,2,0)	
	D = term(1/2,0, 4)
	E = term(-2,1,3)
	F = term(3,2,2)
	G = term(-2,3,1)
	H = term(1/2,4,0)
	
	#assemble it into an array 
	arr = [C,A,B,D,E,F,G,H]
	#p = DCTaylor(arr, B, 9)
	#p2 = DCTaylor(arr, B, 10)
	#Poly(p2)
	p= DCpickdegree(arr, 4,1000)
	Poly(p)
	#Poly(arr)
	#Poly(lastnterms(p, 30))
end


# ╔═╡ 92aff3ec-89e2-4940-bd1d-6a8fd997ea6a
Main5() #New function 

# ╔═╡ 0482deeb-e496-4b7e-b55e-2120f4f23b95
function Main4()
	# Build your terms here, term(coeficient, x degree, xi degree)
	A = term(1,0,2)
	B = term(1,4,0)
	C = term(1000,2,4)
	#D = term(1,2,4)
	
	#assemble it into an array 
	arr = [A,B,C]
	DegreeofC = C.x+C.xi
	#input your function(array, degree you want to push past, number of taylor expansions terms)
	
	#Poly(arr)
	p = youPick2n(arr, DegreeofC, 20 )
	Poly(lastnterms(p, 10))
	#Poly(p)    #this function hurts the computer but shows everything 
	#Poly(arr)S

end


# ╔═╡ 674b60e2-6f17-4c8f-b63f-c29001c1f533
# ╠═╡ show_logs = false
Main4() 

# ╔═╡ fced6cb5-5c6d-4b4d-a177-f73f23ef7d0d
function Main3() #testing for if you can calculate terms separately 
	# Build your terms here, term(coeficient, x degree, xi degree)
	A = term(1,0,2)
	B = term(1,10,0)
	C = term(2.3,13,2)
	D = term(4, 4, 11)
	
	#assemble it into an array 
	arr = [A,B,C,D]
	partialxi = findXp(findP(arr, 15))[2]
	partialx = findXp(findP(arr, 15))[1]

	
	Separately = add(FullXp(arr, [partialxi[1]], [partialx[1]]), FullXp(arr, [partialxi[2]], [partialx[2]]))

	Separately  = add(FullXp(Separately, [partialxi[1]], [partialx[1]]), FullXp(arr, [partialxi[2]], [partialx[2]]))
	
	Poly(FullXp(FullXp(arr, partialxi, partialx), partialxi, partialx))
	Poly(Separately)
	#input your function(array, degree you want to push past, number of taylor expansions terms)
	
	#Poly(arr)
	#p = youPick2n(arr, 15, 3)
	#lastnterms(p, 90)
	#Poly(p)    #this function hurts the computer but shows everything 
	#Poly(arr)

end


# ╔═╡ 00000000-0000-0000-0000-000000000001
PLUTO_PROJECT_TOML_CONTENTS = """
[deps]
LaTeXStrings = "b964fa9f-0449-5b57-a5c2-d3ea65f4040f"

[compat]
LaTeXStrings = "~1.3.1"
"""

# ╔═╡ 00000000-0000-0000-0000-000000000002
PLUTO_MANIFEST_TOML_CONTENTS = """
# This file is machine-generated - editing it directly is not advised

julia_version = "1.10.0"
manifest_format = "2.0"
project_hash = "a78c9b8551c3a88870a8979d61288bd3fa20c137"

[[deps.LaTeXStrings]]
git-tree-sha1 = "50901ebc375ed41dbf8058da26f9de442febbbec"
uuid = "b964fa9f-0449-5b57-a5c2-d3ea65f4040f"
version = "1.3.1"
"""

# ╔═╡ Cell order:
# ╠═bcf7a41e-6f58-45d5-8224-f9f286a56326
# ╠═dc894286-35b1-4f94-9774-3dd91bf6afa7
# ╠═9114e4a8-b3da-4d56-b75f-271c2597a009
# ╠═5db2345c-af04-4385-83ad-6fa72af2151a
# ╠═5e14048a-bdd6-430e-b4c2-70c429e81a90
# ╠═8a56d05e-b1b1-4f7f-90e7-ea5aa4044db8
# ╟─9953a8fb-2164-431e-9c3c-fde485f81a4e
# ╟─fab98343-ae5a-4cbb-8e1b-0654caadb05f
# ╠═fdda6554-6276-43e6-91ea-87ee30af096d
# ╟─9f1cd2e0-e2bb-4ad4-b947-84c065d0c384
# ╟─b1efab7d-0c4d-484f-a90d-970bb47998fb
# ╟─8ac44a5b-f1f3-47d7-bdbc-3896e5022400
# ╟─812d45ec-7b0f-449d-98c6-c1f29d7c7f47
# ╠═b1e9a030-e15a-47ff-b053-9b716cf5f7b6
# ╠═a15557b3-49d7-4690-b6c9-69630272e828
# ╠═a4395194-877f-4aad-bde2-d92a09616dbb
# ╠═11e415ae-3a88-4f5a-81d1-8da8c0c41048
# ╠═b03b364e-3c7f-46aa-b6b7-7b4eb16e1412
# ╠═8240db49-5fa2-4dcb-b808-30878c3dc1c5
# ╠═89ffed51-2842-46d7-96b7-e67ba44a6eec
# ╠═cb2c203d-abd9-4eed-b9f3-2c645e14a171
# ╠═5855996d-676d-4c23-8522-dcbe550bd278
# ╠═78b1d53b-b859-4cf7-96d9-97c6f5510909
# ╠═dff3fbb3-5510-4fd1-82a7-8e540b8e73d3
# ╟─c342c6f1-5737-4617-9341-332ed6cfcdef
# ╠═bd799c26-57c6-4fb7-906c-ef200c047638
# ╟─4ca3155f-93cb-45d1-b2d1-1db3f1ed611c
# ╠═902fe444-12cb-4405-96fb-b839c70ea0f2
# ╠═cb236f21-a215-468d-b05c-8b0cc11bfd83
# ╠═f22cde20-e89c-4e09-b19d-75235d59983d
# ╠═92aff3ec-89e2-4940-bd1d-6a8fd997ea6a
# ╟─0482deeb-e496-4b7e-b55e-2120f4f23b95
# ╠═674b60e2-6f17-4c8f-b63f-c29001c1f533
# ╟─fced6cb5-5c6d-4b4d-a177-f73f23ef7d0d
# ╟─00000000-0000-0000-0000-000000000001
# ╟─00000000-0000-0000-0000-000000000002
