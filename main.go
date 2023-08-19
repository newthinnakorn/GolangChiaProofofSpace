package main

import (
	"bufio"
	"crypto/rand"
	"crypto/sha256"
	"encoding/binary"
	"encoding/hex"
	"fmt"
	"github.com/pkg/profile"
	"github.com/tunabay/go-bitarray"
	"lukechampine.com/blake3"
	"math/big"
	"net/http"
	_ "net/http/pprof"
	"os"
	"runtime"
	"sort"
	"strings"
	"sync"
	"time"
)

type PlotEntry struct {
	y        []byte
	metadata []byte
	xlxr     []byte
	lid      []byte
	rid      []byte
	id       []byte
	used     bool
}
type F1Entry struct {
	xy          [((k + kExtraBits + k) + 8 - 1) / 8]byte
	BucketIndex int
}
type T1Entry struct {
	y [((k + kExtraBits) + 8 - 1) / 8]byte
	x [((k) + 8 - 1) / 8]byte
}
type Plot struct {
	t1 []PlotEntry
	t2 []PlotEntry
	t3 []PlotEntry
	t4 []PlotEntry
	t5 []PlotEntry
	t6 []PlotEntry
	t7 []PlotEntry
}
type Range struct {
	Start uint64
	End   uint64
}
type chacha8Ctx struct {
	input [16]uint32
}

var F1NumByte = cdiv(k + int(kExtraBits) + k)
var ctx chacha8Ctx
var plot Plot
var kVectorLens = []uint8{0, 0, 1, 2, 4, 4, 3, 2}

const (
	sigma = "expand 32-byte k"
	tau   = "expand 16-byte k"
	k     = 28

	kF1BlockSizeBits int = 512

	// Extra bits of output from the f functions.
	kExtraBits uint8 = 6

	// Convenience variable
	kExtraBitsPow = 1 << kExtraBits //Param_M 64

	// B and C groups which constitute a bucket, or BC group.
	kB       uint64 = 119
	kC       uint64 = 127
	kBC             = kB * kC
	kCInt64         = int64(kC)
	kBInt64         = int64(kB)
	kBCInt64        = int64(kBC)
	maxValue        = uint64(1) << uint64(k)
)

func U8to32Little(p []byte) uint32 {
	return binary.LittleEndian.Uint32(p)
}
func U32to8Little(p []byte, v uint32) {
	binary.LittleEndian.PutUint32(p, v)
}
func ROTL32(v, n uint32) uint32 {
	return ((v) << (n)) | ((v) >> (32 - (n)))
}
func ROTATE(v, c uint32) uint32 {
	return ROTL32(v, c)
}
func XOR(v, w uint32) uint32 {
	return (v) ^ (w)
}
func PLUS(v, w uint32) uint32 {
	return (v) + (w)
}
func PLUSONE(v uint32) uint32 {
	return PLUS((v), 1)
}
func QUARTERROUND(a, b, c, d *uint32) {
	*a = PLUS(*a, *b)
	*d = ROTATE(XOR(*d, *a), 16)
	*c = PLUS(*c, *d)
	*b = ROTATE(XOR(*b, *c), 12)
	*a = PLUS(*a, *b)
	*d = ROTATE(XOR(*d, *a), 8)
	*c = PLUS(*c, *d)
	*b = ROTATE(XOR(*b, *c), 7)
}
func chacha8Keysetup(x *chacha8Ctx, k []byte, kbits uint32, iv []byte) {
	var constants string

	x.input[4] = U8to32Little(k[0:])
	x.input[5] = U8to32Little(k[4:])
	x.input[6] = U8to32Little(k[8:])
	x.input[7] = U8to32Little(k[12:])
	if kbits == 256 { // recommended
		k = k[16:]
		constants = sigma
	} else { // kbits == 128
		constants = tau
	}
	x.input[8] = U8to32Little(k[0:])
	x.input[9] = U8to32Little(k[4:])
	x.input[10] = U8to32Little(k[8:])
	x.input[11] = U8to32Little(k[12:])
	x.input[0] = U8to32Little([]byte(constants)[0:])
	x.input[1] = U8to32Little([]byte(constants)[4:])
	x.input[2] = U8to32Little([]byte(constants)[8:])
	x.input[3] = U8to32Little([]byte(constants)[12:])
	if iv != nil {
		x.input[14] = U8to32Little(iv[0:])
		x.input[15] = U8to32Little(iv[4:])
	} else {
		x.input[14] = 0
		x.input[15] = 0
	}
}
func chacha8GetKeystream(x *chacha8Ctx, pos uint64, nBlocks uint32, c []byte) {
	var x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15 uint32
	var j0, j1, j2, j3, j4, j5, j6, j7, j8, j9, j10, j11, j12, j13, j14, j15 uint32
	var i int

	j0 = x.input[0]
	j1 = x.input[1]
	j2 = x.input[2]
	j3 = x.input[3]
	j4 = x.input[4]
	j5 = x.input[5]
	j6 = x.input[6]
	j7 = x.input[7]
	j8 = x.input[8]
	j9 = x.input[9]
	j10 = x.input[10]
	j11 = x.input[11]
	j12 = uint32(pos)
	j13 = uint32(pos >> 32)
	j14 = x.input[14]
	j15 = x.input[15]

	for nBlocks > 0 {
		x0 = j0
		x1 = j1
		x2 = j2
		x3 = j3
		x4 = j4
		x5 = j5
		x6 = j6
		x7 = j7
		x8 = j8
		x9 = j9
		x10 = j10
		x11 = j11
		x12 = j12
		x13 = j13
		x14 = j14
		x15 = j15
		for i = 8; i > 0; i -= 2 {
			QUARTERROUND(&x0, &x4, &x8, &x12)
			QUARTERROUND(&x1, &x5, &x9, &x13)
			QUARTERROUND(&x2, &x6, &x10, &x14)
			QUARTERROUND(&x3, &x7, &x11, &x15)
			QUARTERROUND(&x0, &x5, &x10, &x15)
			QUARTERROUND(&x1, &x6, &x11, &x12)
			QUARTERROUND(&x2, &x7, &x8, &x13)
			QUARTERROUND(&x3, &x4, &x9, &x14)
		}
		x0 = PLUS(x0, j0)
		x1 = PLUS(x1, j1)
		x2 = PLUS(x2, j2)
		x3 = PLUS(x3, j3)
		x4 = PLUS(x4, j4)
		x5 = PLUS(x5, j5)
		x6 = PLUS(x6, j6)
		x7 = PLUS(x7, j7)
		x8 = PLUS(x8, j8)
		x9 = PLUS(x9, j9)
		x10 = PLUS(x10, j10)
		x11 = PLUS(x11, j11)
		x12 = PLUS(x12, j12)
		x13 = PLUS(x13, j13)
		x14 = PLUS(x14, j14)
		x15 = PLUS(x15, j15)

		j12 = PLUSONE(j12)
		if j12 == 0 {
			j13 = PLUSONE(j13)
			/* stopping at 2^70 bytes per nonce is user's responsibility */
		}

		U32to8Little(c[0:], x0)
		U32to8Little(c[4:], x1)
		U32to8Little(c[8:], x2)
		U32to8Little(c[12:], x3)
		U32to8Little(c[16:], x4)
		U32to8Little(c[20:], x5)
		U32to8Little(c[24:], x6)
		U32to8Little(c[28:], x7)
		U32to8Little(c[32:], x8)
		U32to8Little(c[36:], x9)
		U32to8Little(c[40:], x10)
		U32to8Little(c[44:], x11)
		U32to8Little(c[48:], x12)
		U32to8Little(c[52:], x13)
		U32to8Little(c[56:], x14)
		U32to8Little(c[60:], x15)

		c = c[64:]
		nBlocks--
	}
}
func cdiv(a int) int {
	return (a + 8 - 1) / 8
}
func PedingBitsWithlen(intToBitArray *bitarray.BitArray, numlen int) *bitarray.BitArray {
	if intToBitArray.Len() > numlen { // if intToBitArray.Len()) > numlen remove L
		intToBitArrayPad := bitarray.MustParse("")

		intToBitArrayPad = intToBitArray.Slice(intToBitArray.Len()-numlen, intToBitArray.Len())
		return intToBitArrayPad
	} else if intToBitArray.Len() < numlen { // if intToBitArray.Len()) < numlen Pad 0 L
		numZero := numlen - intToBitArray.Len()
		pad := bitarray.NewZeroFilled(numZero)
		intToBitArrayPad := pad.Append(intToBitArray)
		return intToBitArrayPad
	} else {
		return intToBitArray // return original
	}

}
func PedingBits(intToBitArray *bitarray.BitArray) *bitarray.BitArray {
	if intToBitArray.Len()%8 != 0 {
		pad := bitarray.NewZeroFilled(intToBitArray.NumPadding())
		return pad.Append(intToBitArray)
	}
	return intToBitArray
}
func PedingBitsRight(intToBitArray *bitarray.BitArray) *bitarray.BitArray {
	intToBitArrayPad := bitarray.MustParse("")
	pad := bitarray.NewZeroFilled(intToBitArray.NumPadding())
	intToBitArrayPad = intToBitArrayPad.Append(intToBitArray, pad)
	return intToBitArrayPad
}
func padByteLeft(in []byte, bytelen int) []byte {
	out := make([]byte, bytelen) //byte8 = 64bit
	if len(in) > bytelen {
		fmt.Println(bytelen, len(in), in, bytelen-len(in))
	}

	copy(out[bytelen-len(in):], in)
	return out
}
func appendExtraDataPadRight(outputBits, L *bitarray.BitArray) *bitarray.BitArray { // pad right
	extraData := L.Slice(0, min(int(kExtraBits), L.Len()))
	if extraData.Len() < int(kExtraBits) {
		paddingSize := int(kExtraBits) - extraData.Len()
		padding := bitarray.NewZeroFilled(paddingSize)
		extraData = padding.Append(extraData)
	}

	return outputBits.Append(extraData)
}
func min(a, b int) int {
	if a < b {
		return a
	}
	return b
}

// Convert a string of bits to a byte slice
func bitsStringToBytes(bitString string) []byte {
	// Pad the bit string if necessary
	if len(bitString)%8 != 0 {
		padLen := 8 - len(bitString)%8
		bitString = strings.Repeat("0", padLen) + bitString
	}

	// Convert the bit string to a byte slice
	byteSlice := make([]byte, len(bitString)/8)
	for i := 0; i < len(bitString); i += 8 {
		byteSlice[i/8] = bitsToByte(bitString[i : i+8])
	}

	return byteSlice
}

// Convert a string of 8 bits to a byte
func bitsToByte(bits string) byte {
	b := byte(0)
	for i, c := range bits {
		if c == '1' {
			b |= 1 << (7 - i)
		}
	}
	return b
}
func parallelMergeSort(plotEntries []T1Entry, numGoroutines int) {
	var wg sync.WaitGroup
	wg.Add(1)
	mergeSort(plotEntries, numGoroutines, &wg)
	wg.Wait()
}
func mergeSort(plotEntries []T1Entry, numGoroutines int, wg *sync.WaitGroup) {
	defer wg.Done()

	n := len(plotEntries)
	if n <= 1 {
		return
	}

	if numGoroutines > 1 {
		numGoroutines /= 2
		var wg2 sync.WaitGroup
		wg2.Add(2)

		mid := n / 2
		go mergeSort(plotEntries[:mid], numGoroutines, &wg2)
		go mergeSort(plotEntries[mid:], numGoroutines, &wg2)
		wg2.Wait()
	} else {
		sort.Slice(plotEntries, func(i, j int) bool {
			return lessSlice(plotEntries[i].y[:], plotEntries[j].y[:])
		})
	}

	merge(plotEntries)
}
func merge(plotEntries []T1Entry) {
	n := len(plotEntries)
	mid := n / 2

	i, j := 0, mid
	temp := make([]T1Entry, 0, n)
	for i < mid && j < n {
		if lessSlice(plotEntries[i].y[:], plotEntries[j].y[:]) {
			temp = append(temp, plotEntries[i])
			i++
		} else {
			temp = append(temp, plotEntries[j])
			j++
		}
	}

	temp = append(temp, plotEntries[i:mid]...)
	temp = append(temp, plotEntries[j:]...)
	copy(plotEntries, temp)
}
func lessSlice(a, b []byte) bool {
	for i := 0; i < len(a) && i < len(b); i++ {
		if a[i] < b[i] {
			return true
		} else if a[i] > b[i] {
			return false
		}
	}
	return len(a) < len(b)
}
func NewBits(intvalue *big.Int, len int) *bitarray.BitArray {
	//if intvalue > len = pad 0 in left

	idInttobitarray := bitarray.NewFromInt(intvalue)
	if idInttobitarray.Len() < len {
		ZeroFilled := bitarray.NewZeroFilled(len - idInttobitarray.Len())
		output := bitarray.MustParse("")
		output = output.Append(ZeroFilled, idInttobitarray)
		return output
	} else {
		output := bitarray.MustParse("")
		output = idInttobitarray.Slice(idInttobitarray.Len()-len, idInttobitarray.Len())
		return output
	}
}
func calculatePercent(value float64, total float64) float64 {
	if total == 0 {
		return 0.0
	}
	return (value / total) * 100.0
}
func calbucket(left T1Entry, right T1Entry, tableIndex int, metadataSize int, k int) (f, c *bitarray.BitArray) {

	yL := new(big.Int).SetBytes(left.y[:])
	xL := new(big.Int).SetBytes(left.x[:])
	xR := new(big.Int).SetBytes(right.x[:])

	//convert back to int
	y := NewBits(yL, k+int(kExtraBits))
	lx := NewBits(xL, metadataSize)
	rx := NewBits(xR, metadataSize)

	input := bitarray.MustParse("")
	if tableIndex < 4 {
		c = bitarray.MustParse("")
		c = c.Append(lx, rx)
		input = input.Append(y, c)

	} else {
		input = input.Append(y, lx, rx)
	}

	buf2byte, _ := PedingBitsRight(input).Bytes()

	blake3Hash := blake3.New(32, nil)
	_, err := blake3Hash.Write(buf2byte)
	if err != nil {
		return nil, nil
	}
	hashBytes := blake3Hash.Sum(nil)

	value := binary.BigEndian.Uint64(hashBytes) //***

	newfx := value >> (64 - (k + int(kExtraBits)))

	if tableIndex < 4 {
		// c is already computed
	} else if tableIndex < 7 {

		var vectorlen = kVectorLens[tableIndex+1]
		var startByte = (k + int(kExtraBits)) / 8
		var endBit = k + int(kExtraBits) + k*int(vectorlen)
		var endByte = cdiv(endBit)

		c = bitarray.NewBufferFromByteSlicePartial(hashBytes[startByte:endByte], 0, (endByte-startByte)*8).BitArray().Slice((k+int(kExtraBits))%8, endBit-startByte*8)

	}

	f = NewBits(big.NewInt(int64(newfx)), k+int(kExtraBits))

	return f, c
}
func BucketID(y uint64) uint64 {
	return y / kBC
}
func findMatches(matchingShiftsC [][]int, bucketL []T1Entry, bucketR []T1Entry) [][]int {
	var matches [][]int
	RBids := [kCInt64][]int64{}
	RPositions := [kCInt64][]int64{}

	yLParity := new(big.Int).SetBytes(bucketL[0].y[:]).Int64()
	parity := (yLParity / kBCInt64) % 2

	for posR, y2 := range bucketR {
		yR := new(big.Int).SetBytes(y2.y[:]).Int64()
		RBid := (yR % kBCInt64) / kCInt64
		RCid := yR % kCInt64
		RBids[RCid] = append(RBids[RCid], RBid)
		RPositions[RCid] = append(RPositions[RCid], int64(posR))
	}

	for posL, y1 := range bucketL {
		yL := new(big.Int).SetBytes(y1.y[:]).Int64()
		ylBid := (yL % kBCInt64) / kCInt64
		ylCid := yL % kCInt64

		for m := int64(0); m < kExtraBitsPow; m++ {
			targetBid := ylBid + m
			targetCid := ylCid + int64(matchingShiftsC[int(parity)][int(m)])
			targetBid %= kBInt64
			targetCid %= kCInt64

			RBidList := RBids[targetCid]
			RPositionList := RPositions[targetCid]
			RBidListLen := len(RBidList)

			for i := 0; i < RBidListLen; i++ {
				if targetBid == RBidList[i] {
					ylBucket := yL / kBCInt64

					yrBucket := new(big.Int).SetBytes(bucketR[RPositionList[i]].y[:]).Int64() / kBCInt64
					if ylBucket+1 == yrBucket {
						matches = append(matches, []int{posL, int(RPositionList[i])})
					}
				}
			}
		}
	}
	return matches
}
func parallelBucketCreation(buckets map[uint32][]T1Entry, data []byte) {
	YXNumByte := cdiv(k + int(kExtraBits) + k)
	allEntries := len(data) / YXNumByte

	numCPU := runtime.NumCPU()
	chunkSize := (allEntries + numCPU - 1) / numCPU
	if chunkSize > allEntries {
		chunkSize = allEntries
	}
	fmt.Println(maxValue, "Start LoadFile to []PlotEntry")
	// Create a wait group to synchronize goroutines

	var wg sync.WaitGroup
	var mutex sync.Mutex

	wg.Add(numCPU)
	for j := uint64(0); j < uint64(numCPU); j++ {
		start := j * uint64(chunkSize)
		end := start + uint64(chunkSize)
		if end > uint64(allEntries) {
			end = uint64(allEntries)
		}
		go func(startIndex, endIndex uint64) {
			defer wg.Done()
			//fmt.Println("Report| YXNumByte:", YXNumByte, "allEntries:", allEntries, "chunkSize:", chunkSize, "startIndex:", startIndex, "endIndex:", endIndex)
			startByte := 0
			localBuckets := make(map[uint32][]T1Entry)
			var bucketID uint32
			var y *bitarray.BitArray
			var x *bitarray.BitArray
			var entryBitArray *bitarray.BitArray
			var yByte []byte
			var xByte []byte
			for i := startIndex; i < endIndex; i++ {
				if i >= maxValue {
					break
				}
				startByte = int(i) * YXNumByte
				entryBitArray = bitarray.NewBufferFromByteSlice(data[startByte : startByte+YXNumByte]).BitArray()
				y = entryBitArray.Slice(entryBitArray.Len()-(k+int(kExtraBits)+k), entryBitArray.Len()-(k+int(kExtraBits)+k)+k+int(kExtraBits))
				x = entryBitArray.Slice(entryBitArray.Len()-k, entryBitArray.Len())
				bucketID = uint32(BucketID(y.ToUint64()))

				if _, ok := localBuckets[bucketID]; !ok {
					localBuckets[bucketID] = make([]T1Entry, 0, 1) // Adjust the initial capacity as needed
				}
				yByte, _ = PedingBits(y).Bytes()
				xByte, _ = PedingBits(x).Bytes()
				newEntry := T1Entry{
					y: [((k + kExtraBits) + 8 - 1) / 8]byte(yByte),
					x: [((k) + 8 - 1) / 8]byte(xByte),
				}
				localBuckets[bucketID] = append(localBuckets[bucketID], newEntry)
			}
			mutex.Lock()
			for BId, LoEntries := range localBuckets {
				buckets[BId] = append(buckets[BId], LoEntries...)
			}
			mutex.Unlock()
		}(start, end)
	}
	wg.Wait()
}
func parallelMergeSortBuckets(buckets map[uint32][]T1Entry, numCPU int) {
	sem := make(chan struct{}, numCPU)
	var wg sync.WaitGroup
	wg.Add(len(buckets))

	for _, entries := range buckets {
		sem <- struct{}{} // Acquire semaphore
		go func(entries []T1Entry) {
			defer func() { <-sem }() // Release semaphore
			defer wg.Done()
			parallelMergeSort(entries, numCPU)
		}(entries)
	}

	wg.Wait()
}
func loadDataFromFile(filename string, k int) (map[uint32][]T1Entry, error) {
	buckets := make(map[uint32][]T1Entry)
	startTimeReadFile := time.Now()
	fmt.Println(filename, "ReadFile ")
	data, err := os.ReadFile(filename)
	if err != nil {
		fmt.Println(err)
	}
	timeElapsed := time.Since(startTimeReadFile)
	fmt.Println(filename, "End ReadFile", len(data), "time took ", timeElapsed)

	parallelBucketCreation(buckets, data)

	fmt.Println(filename, "Start parallelMergeSortBuckets:", len(buckets))
	startTimeReadFile = time.Now()
	parallelMergeSortBuckets(buckets, runtime.NumCPU())
	timeElapsed = time.Since(startTimeReadFile)
	fmt.Println(filename, "End parallelMergeSortBuckets:", len(buckets), "time took ", timeElapsed)

	startload := time.Now()
	fmt.Println("Start runtime.GC()")
	runtime.GC()
	timeElapsed = time.Since(startload)
	fmt.Println("END runtime.GC() time took ", timeElapsed)
	return buckets, nil
}
func GoMatching(b uint32, matchingShiftsC [][]int, tableIndex uint8, metadataSize int, k int, leftBucket, rightBucket []T1Entry, wg *sync.WaitGroup, goroutineSem chan struct{}) {
	//start := time.Now()
	defer wg.Done()
	m := 0

	for _, match := range findMatches(matchingShiftsC, leftBucket, rightBucket) {
		_, _ = calbucket(leftBucket[match[0]], rightBucket[match[1]], int(tableIndex+1), metadataSize, k)
		m++
	}
	//timeElapsed := time.Since(start)
	//fmt.Printf("%d %d %d %d | time took %s \n", b, len(leftBucket), len(rightBucket), m, timeElapsed)

	<-goroutineSem
}
func FindIndexID(Entries []PlotEntry, value uint64) uint64 {
	reuseBigID := new(big.Int)
	for i, v := range Entries {
		if reuseBigID.SetBytes(v.id).Uint64() == value {
			return uint64(i)
		}
	}
	return 0
}
func divmod(numerator, denominator uint64) (quotient, remainder uint64) {
	quotient = numerator / denominator
	remainder = numerator % denominator
	return
}
func CompareProofBits(left, right *bitarray.BitArray, k uint8) int {
	// Compares starting at last element, then second to last, etc.

	// Compares two lists of k values, L and R. L > R if max(L) > max(R),
	// if there is a tie, the next largest value is compared.

	size := left.Len() / int(k)
	if left.Len() != right.Len() {
		panic("Bit lengths do not match")
	}
	u := 1
	for i := size - 1; i >= 0; i-- {
		leftVal := left.Slice(int(k)*i, int(k)*(i+1))
		rightVal := right.Slice(int(k)*i, int(k)*(i+1))
		L, _ := PedingBits(leftVal).Bytes()
		R, _ := PedingBits(rightVal).Bytes()
		LB := new(big.Int).SetBytes(L)
		RB := new(big.Int).SetBytes(R)

		if LB.Cmp(RB) == -1 { //L < R
			return -1
		}
		if LB.Cmp(RB) == 1 { //L > R
			return 1
		}
		u++
	}
	return 0 //L = R
}
func ByteAlign(numBits int) int {
	return (numBits + (8-((numBits)%8))%8)
}

func bytesLess(a, b []byte) bool {
	for i := 0; i < len(a) && i < len(b); i++ {
		if a[i] != b[i] {
			return a[i] < b[i]
		}
	}
	return len(a) < len(b)
}
func RandomByteArray(size int) ([]byte, error) {
	// Create a byte array of the given size
	byteArray := make([]byte, size)

	// Read random bytes from the crypto/rand package
	_, err := rand.Read(byteArray)
	if err != nil {
		return nil, err
	}

	return byteArray, nil
}
func ByteToHexString(byteArray []byte) string {
	hexString := hex.EncodeToString(byteArray)
	return hexString
}
func f1N(k int, x uint64) PlotEntry {

	BitsX := bitarray.NewFromInt(big.NewInt(int64(x)))
	BitsXPadToKBits := PedingBitsWithlen(BitsX, int(uint64(k)))

	q, r := (int(x)*k)/kF1BlockSizeBits, (int(x)*k)%kF1BlockSizeBits

	if r+k <= kF1BlockSizeBits {
		cipherBlock := make([]byte, kF1BlockSizeBits/8) //64 byte 512bits/8
		chacha8GetKeystream(&ctx, uint64(q), 1, cipherBlock)
		ByteToBitArray := bitarray.NewBufferFromByteSlice(cipherBlock)
		ciphertextFillets := ByteToBitArray.Slice(r, r+k)
		appendExtraData := appendExtraDataPadRight(ciphertextFillets.BitArray(), BitsXPadToKBits) // Adds the first few bits of L to the end of the output, production k + kExtraBits of output
		buf1PedingBits := PedingBitsWithlen(appendExtraData, k+int(kExtraBits))                   //then PedingBits befor save to PlotEntry *(Bytes())
		Ybyte := bitsStringToBytes(PedingBits(buf1PedingBits.BitArray()).String())

		Xbyte := bitsStringToBytes(BitsXPadToKBits.String())

		newEntry := PlotEntry{
			y:        Ybyte,
			metadata: Xbyte,
		}
		return newEntry
	} else {
		cipherBlock1 := make([]byte, kF1BlockSizeBits/8) //64 byte 512bits/8
		chacha8GetKeystream(&ctx, uint64(q), 1, cipherBlock1)
		ByteToBitArrayone := bitarray.NewBufferFromByteSlice(cipherBlock1)
		BlockFillet1 := ByteToBitArrayone.Slice(r, ByteToBitArrayone.Len())

		cipherBlock2 := make([]byte, kF1BlockSizeBits/8) //64 byte 512bits/8
		chacha8GetKeystream(&ctx, uint64(q+1), 1, cipherBlock2)
		ByteToBitArrayTwo := bitarray.NewBufferFromByteSlice(cipherBlock2)
		BlockFillet2 := ByteToBitArrayTwo.Slice(0, r+k-kF1BlockSizeBits)

		buf := bitarray.MustParse("")
		buf = buf.Append(BlockFillet1, BlockFillet2)

		appendExtraData := appendExtraDataPadRight(buf.BitArray(), BitsXPadToKBits) // Adds the first few bits of L to the end of the output, production k + kExtraBits of output
		buf1PedingBits := PedingBitsWithlen(appendExtraData, k+int(kExtraBits))     //then PedingBits befor save to PlotEntry *(Bytes())
		Ybyte := bitsStringToBytes(PedingBits(buf1PedingBits.BitArray()).String())

		Xbyte := bitsStringToBytes(BitsXPadToKBits.String())

		newEntry := PlotEntry{
			y:        Ybyte,
			metadata: Xbyte,
		}
		return newEntry
	}
}
func MFast(left T1Entry, right T1Entry) bool {

	yL := new(big.Int).SetBytes(left.y[:]).Int64()
	yR := new(big.Int).SetBytes(right.y[:]).Int64()

	BucketIDL := yL / kBCInt64
	BucketIDR := yR / kBCInt64

	if BucketIDL+1 == BucketIDR {
		yLBC := yL % kBCInt64
		yRBC := yR % kBCInt64
		yLBCDivC := yLBC / kCInt64
		yRBCDivC := yRBC / kCInt64

		yLBCModC := yLBC % kCInt64
		yRBCModC := yRBC % kCInt64

		BucketIDLMod2 := BucketIDL % 2

		for m := int64(0); m < kExtraBitsPow; m++ {
			cIDDiff := yRBCModC - yLBCModC - (2*m+BucketIDLMod2)*(2*m+BucketIDLMod2)
			bIDDiff := yRBCDivC - yLBCDivC - m

			if bIDDiff%kBInt64 == 0 && cIDDiff%kCInt64 == 0 {
				return true
			}
		}
	}
	return false
}
func BitarrayTobyte(EntryBitarray *bitarray.BitArray) []byte {
	res, _ := PedingBits(EntryBitarray).Bytes()
	return res
}
func GetInputs(id uint64, table_index uint8, k int) []*bitarray.BitArray {

	tables := []*[]PlotEntry{nil, &plot.t1, &plot.t2, &plot.t3, &plot.t4, &plot.t5, &plot.t6, &plot.t7}
	if table_index >= uint8(len(tables)) {
		// Handle the case when the table index is out of range
		return nil
	}

	entry := (*tables[table_index])[FindIndexID(*tables[table_index], id)]
	positionx1 := binary.BigEndian.Uint64(padByteLeft(entry.lid, 8))
	positionx2 := binary.BigEndian.Uint64(padByteLeft(entry.rid, 8))

	var ret []*bitarray.BitArray
	if table_index == 2 {
		L_Entry := (*tables[1])[FindIndexID(*tables[1], positionx1)]
		R_Entry := (*tables[1])[FindIndexID(*tables[1], positionx2)]

		ret = make([]*bitarray.BitArray, 2)
		ret[0] = PedingBitsWithlen(bitarray.NewBufferFromByteSlice(L_Entry.metadata).BitArray(), k)
		ret[1] = PedingBitsWithlen(bitarray.NewBufferFromByteSlice(R_Entry.metadata).BitArray(), k)

	} else {
		left := GetInputs(positionx1, table_index-1, k)
		right := GetInputs(positionx2, table_index-1, k)

		ret = make([]*bitarray.BitArray, len(left)+len(right))
		copy(ret, left)
		copy(ret[len(left):], right)
	}

	// Memoize the result

	return ret
}
func ProofToPlot(proof *bitarray.BitArray, k uint8) *bitarray.BitArray {
	var L *bitarray.BitArray
	var R *bitarray.BitArray
	for tableIndex := uint8(1); tableIndex < 7; tableIndex++ {
		var newProof *bitarray.BitArray
		size := int(k) * (1 << (tableIndex - 1))
		for j := 0; j < (1 << (7 - tableIndex)); j += 2 {
			L = proof.Slice(j*size, (j+1)*size)
			R = proof.Slice((j+1)*size, (j+2)*size)
			if CompareProofBits(L, R, k) == 1 { //switch
				newLR := R.Append(L)
				newProof = newProof.Append(newLR)
				//fmt.Println(tableIndex, size, j, j+1, "(", j*size, (j+1)*size, ")", "(", (j+1)*size, (j+2)*size, ")", L, R, "true", newLR)
			} else {
				newLR := L.Append(R)
				newProof = newProof.Append(newLR) //no switch
				//fmt.Println(tableIndex, size, j, j+1, "(", j*size, (j+1)*size, ")", "(", (j+1)*size, (j+2)*size, ")", L, R, "False", newLR)
			}

		}
		proof = newProof
	}
	return proof
}
func GetQualityString(k uint8, proof *bitarray.BitArray, qualityIndex *bitarray.BitArray, challenge []byte) *bitarray.BitArray {

	// Hashes two of the x values, based on the quality index
	// Pad the bit string if necessary

	hashInput := make([]byte, len(challenge)+(ByteAlign(int(2*k))/8))
	copy(hashInput[:32], challenge)

	X1 := proof.Slice(int(k)*int(qualityIndex.ToUint64()*2), int(k)*(int(qualityIndex.ToUint64()*2)+1))
	X2 := proof.Slice(int(k)*(int(qualityIndex.ToUint64()*2)+1), int(k)*(int(qualityIndex.ToUint64()*2)+2))
	X1X2Bits := X1.Append(X2)
	//fmt.Println(X1,X2)

	X1X2BitsToByte, _ := PedingBits(PedingBitsRight(X1X2Bits)).Bytes()
	copy(hashInput[32:], X1X2BitsToByte)

	//fmt.Println(hexString,len(hexString))
	hash := sha256.Sum256(hashInput)

	QualityStringBits := bitarray.NewBufferFromByteSlice(hash[:]).BitArray()
	return QualityStringBits
}

/*
func PlotToProof(proof *bitarray.BitArray, k uint8) *bitarray.BitArray {
	// Calculates f1 for each of the inputs
	var results []PlotEntry
	var xs *bitarray.BitArray
	for i := 0; i < 64; i++ {
		x := proof.Slice(i*int(k), (i+1)*int(k)).ToUint64()
		result := f1N(int(k), x)
		results = append(results, result)
		xs = xs.Append(PedingBitsWithlen(bitarray.NewBufferFromByteSlice(result.metadata).BitArray(), int(k)))
		//fmt.Println("xs:", PedingBitsWithlen(bitarray.NewBufferFromByteSlice(result.y).BitArray(), uint64(k+6)))
	}

	// The plotter calculates f1..f7, and at each level, decides to swap or not swap. Here, we
	// are doing a similar thing, we swap left and right, such that we end up with proof
	// ordering.
	for tableIndex := uint8(2); tableIndex < 8; tableIndex++ {
		var newXs *bitarray.BitArray
		var newResults []PlotEntry
		// Computes the output pair (fx, new_metadata)
		//fmt.Println("tableIndex :", tableIndex)
		// Iterates through pairs of things, starts with 64 things, then 32, etc, up to 2.
		for i := 0; i < len(results); i += 2 {
			var newOutput PlotEntry
			var Fx []byte
			var C []byte

			// Compares the buckets of both ys to see which one goes on the left and which one goes on the right
			if bitarray.NewBufferFromByteSlice(results[i].y).Uint64() < bitarray.NewBufferFromByteSlice(results[i+1].y).Uint64() {
				FxOutput, COutput := calbucket(
					results[i],
					results[i+1],
					tableIndex,
					int(k),
				)
				//fmt.Println("<", FxOutput, COutput)
				Fx, _ = PedingBits(FxOutput).Bytes()
				C, _ = PedingBits(COutput).Bytes()

				start := uint64(k) * uint64(i) * (1 << (tableIndex - 2))
				end := uint64(k) * uint64(i+2) * (1 << (tableIndex - 2))
				newXs = newXs.Append(xs.Slice(int(start), int(end)))
			} else {
				// Here we switch the left and the right
				FxOutput, COutput := calbucket(
					results[i+1],
					results[i],
					tableIndex,
					int(k),
				)
				//fmt.Println(">", FxOutput, COutput)
				Fx, _ = PedingBits(FxOutput).Bytes()
				C, _ = PedingBits(COutput).Bytes()
				start := uint64(k) * uint64(i) * (1 << (tableIndex - 2))
				start2 := uint64(k) * uint64(i+1) * (1 << (tableIndex - 2))
				end := uint64(k) * uint64(i+2) * (1 << (tableIndex - 2))

				newXs = newXs.Append(xs.Slice(int(start2), int(end)))
				newXs = newXs.Append(xs.Slice(int(start), int(start2)))
			}

			newOutput = PlotEntry{
				y:        Fx,
				metadata: C,
			}
			newResults = append(newResults, newOutput)
		}

		// Advances to the next table
		// xs is a concatenation of all 64 x values, in the current order. Note that at each
		// iteration, we can swap several parts of xs
		results = newResults
		xs = newXs
	}

	var orderedProof *bitarray.BitArray

	for i := uint8(0); i < 64; i++ {
		orderedProof = orderedProof.Append(xs.Slice(int(uint64(i)*uint64(k)), int((uint64(i)+1)*uint64(k))))

	}

	return orderedProof
}
*/

func computTables(maxValue uint64, TmpFileCount uint64, BucketCount uint64, k int, table_index uint8) {
	start := time.Now()
	metadataSize := int(kVectorLens[table_index+1]) * k //0, 0, 1, 2, 4, 4, 3, 2
	// Precomputation necessary to compute matches
	matchingShiftsC := make([][]int, 2)
	for i := 0; i < 2; i++ {
		matchingShiftsC[i] = make([]int, kCInt64)
	}

	for parity := 0; parity < 2; parity++ {
		for r := int64(0); r < kExtraBitsPow; r++ {
			v := ((2*r + int64(parity)) * (2*r + int64(parity))) % kCInt64
			matchingShiftsC[parity][r] = int(v)
		}
	}

	fmt.Println("Computing table ", table_index+1)
	var wg sync.WaitGroup
	numCPU := runtime.NumCPU() - 1
	entryCount := 0

	FirstLoad := true
	NeedLoad := false
	LoopTmpFile := uint64(0)
	bucketsContinue := make([]T1Entry, 0, 1) // Adjust the initial capacity as needed
	goroutineSem := make(chan struct{}, numCPU)
	buckets := make(map[uint32][]T1Entry)

	for b := uint32(0); b < uint32(BucketCount); b++ {
		if NeedLoad == true || FirstLoad == true {
			startload := time.Now()
			if LoopTmpFile == TmpFileCount {
				entryCount = entryCount + len(bucketsContinue)
				fmt.Println("Break LoopTmpFile > TmpFileCount")
				break
			}

			fileName := fmt.Sprintf("E://output/Bucket_%d.tmp", LoopTmpFile)
			var err error
			buckets, err = loadDataFromFile(fileName, k)
			if err != nil {
				fmt.Println("err loadDataFromFile:", err)
			}

			if NeedLoad == true {
				buckets[b] = bucketsContinue
				bucketsContinue = make([]T1Entry, 0, 1) // Adjust the initial capacity as needed
				fmt.Println(fileName, "buckets NeedLoad at:", b+1, len(buckets[b]))
				NeedLoad = false
			}

			timeElapsed := time.Since(startload)
			fmt.Println(fileName, "LoadData time took ", timeElapsed)

			LoopTmpFile++
			FirstLoad = false

			fmt.Println(fileName, "Find Matching... buckets : ", len(buckets))
			fmt.Println("")
		}

		if len(buckets[b+1]) == 0 {
			bucketsContinue = buckets[b]
			buckets = make(map[uint32][]T1Entry)
			fmt.Println("R buckets Continue at:", b+1, len(bucketsContinue))
			fmt.Println("create bucketsContinue:", b)
			NeedLoad = true
			b--
			fmt.Println("Backward 1 step to :", b)
			continue
		}

		if len(buckets[b]) > 0 && len(buckets[b+1]) > 0 {
			entryCount = entryCount + len(buckets[b])
		}

		//fmt.Println(b, b+1, BucketCount)
		wg.Add(1)
		goroutineSem <- struct{}{}
		go GoMatching(b, matchingShiftsC, table_index, metadataSize, k, buckets[b], buckets[b+1], &wg, goroutineSem)
	}

	wg.Wait()
	fmt.Println("End:", entryCount, maxValue)
	timeElapsed := time.Since(start)
	fmt.Printf("computTables time took %s \n", timeElapsed)
}
func f1(ranges []Range, k int, start uint64, end uint64, waitingRoomEntries chan []F1Entry, wg *sync.WaitGroup) {
	defer wg.Done()
	F1NumBits := F1NumByte * 8            // แปลง F1NumByte เป็น bits
	Buffer := (2 * 1000000) / (F1NumByte) //กำหนด buffer MB และหารค่าว่าสามารถใส่ F1 ได้กี่ Entries *Buffer ในที่นี้คือจำนวน index สูงสุดของ bufferPool
	NumBlock := uint64(50000)             //จำนวน Block ที่ต้องการให้ Chacha8  gen ออกมาใน 1 ครั้ง (1block = 512bits)
	bufferPool := make([]F1Entry, Buffer) //หลังจาก คำนวณ F1 จะเก็บไว้ในบัพเฟอร์นี้

	Clen := 0         //init index เริ่มต้นของบับเฟอร์ เราจะ +1 ทุกครั้งที่มีการเพิ่มบัฟเฟอร์ bufferPool
	currentX := start // init x ปัจจุบัน

	reUseXbyteSlice := make([]byte, 8)                // XbyteSlice จะเก็บไว้ในนี้ และจะถูก reuse ใน x ถัดไป ใช้8Byte เพราะสอดคล้องกับ binary.BigEndian.PutUint64
	reUseXbyteSliceBitLen := len(reUseXbyteSlice) * 8 //คำนวณ bits ของ reUseXbyteSlice

	cipherBlock := make([]byte, (kF1BlockSizeBits*int(NumBlock))/8) //ไว้รับค่า Chacha8 ,ขนาดของ cipherBlock = 512*NumBlock/8 หน่วยเป็น Bytes

	q, r := divmod(currentX*uint64(k), uint64(kF1BlockSizeBits))

	//คำนวณ ChaCha8 Block ของ start(x) ว่าเริ่มต้น Block ไหน
	//init index ของ block ของ
	//คำนวณ r ว่ากำลังอยู่ index ของ block q

	chacha8GetKeystream(&ctx, q, uint32(NumBlock), cipherBlock) //chacha8 bulk gen block ขนาด NumBlock และเก็บไว้ใน cipherBlock slice
	//เราจะทำงานในระดับ bits
	// แต่เนื่องด้วยภาษา Go datatype ที่เล็กที่สุดคือ Byte ดังนั้นเราจึงต้องแปลงในอยู่ในรูปแปป BitArray ในฟอร์มของ ByteArray
	//ดังนั้นในขั้นตอนนี้จะใช้ memory 8 ถึงเท่าของข้อมูลจริง ดังนั้นไม่ควรใช้บัฟเฟอร์ขนาดใหญ่
	//หลังจากคำนวณค่า Y แล้ว เราจะรวม BitArray และ Pack เป็นรูปแบบ Byte ก่อนโยนเข้าบัฟเฟอร์ เพื่อให้ใช้พื้นที่ memory อย่างมีประสิทธิภาพ
	ByteToBitArray := bitarray.NewBufferFromByteSlice(cipherBlock).BitArray() //แปลงเป็น bitarray
	for currentX <= end {
		binary.BigEndian.PutUint64(reUseXbyteSlice, currentX)
		XBits := bitarray.NewFromBytes(reUseXbyteSlice, reUseXbyteSliceBitLen-k, reUseXbyteSliceBitLen-(reUseXbyteSliceBitLen-k))
		BitsXPadToKBits := XBits.Slice(0, int(kExtraBits)) //silce bits 0:6(kExtraBits)
		if r+uint64(k) < uint64(kF1BlockSizeBits)*NumBlock {
			BlockFillet1 := ByteToBitArray.Slice(int(r), int(r+uint64(k)))
			F1 := BlockFillet1.Append(BitsXPadToKBits) // Adds the first few bits of L to the end of the output, production k + kExtraBits of output
			F1AndX, _ := PedingBitsWithlen(F1.Append(XBits), F1NumBits).Bytes()
			yBucket := F1.ToUint64() / kBC

			for i, rg := range ranges {
				if yBucket >= rg.Start && yBucket <= rg.End {
					bufferPool[Clen].BucketIndex = i
					break
				}
			}

			copy(bufferPool[Clen].xy[:], F1AndX)

			currentX++
			Clen++
			r += uint64(k)

			if Clen == Buffer {
				newbufferPool := make([]F1Entry, Buffer)
				copy(newbufferPool, bufferPool)
				waitingRoomEntries <- newbufferPool
				Clen = 0
			}
		} else {
			//r ใหม่ q เดิม

			BlockFillet1 := ByteToBitArray.Slice(int(r), ByteToBitArray.Len()) // r:last

			// ######### Gen new Bulk Block #########
			q, r = divmod(currentX*uint64(k), uint64(kF1BlockSizeBits))
			chacha8GetKeystream(&ctx, q, uint32(NumBlock), cipherBlock)
			ByteToBitArray = bitarray.NewBufferFromByteSlice(cipherBlock).BitArray()
			// ######### Gen new Bulk Block #########

			BlockFillet2 := ByteToBitArray.Slice(0, int(r))
			F1 := BlockFillet1.Append(BlockFillet2, BitsXPadToKBits)

			F1AndX, _ := PedingBitsWithlen(F1.Append(XBits), F1NumBits).Bytes()
			yBucket := F1.ToUint64() / kBC

			for i, rg := range ranges {
				if yBucket >= rg.Start && yBucket <= rg.End {
					bufferPool[Clen].BucketIndex = i
					break
				}
			}

			copy(bufferPool[Clen].xy[:], F1AndX)

			currentX++
			Clen++

			if Clen == Buffer {
				NewbufferPool := make([]F1Entry, Buffer)
				copy(NewbufferPool, bufferPool)
				waitingRoomEntries <- NewbufferPool
				Clen = 0
			}
		}

	}
	if Clen > 0 {
		newbufferPool := make([]F1Entry, Buffer)
		copy(newbufferPool, bufferPool)
		waitingRoomEntries <- newbufferPool[:Clen]
		bufferPool = nil
		newbufferPool = nil
	}
}
func main() {
	defer profile.Start(profile.MemProfile).Stop()
	go func() {
		http.ListenAndServe(":8080", nil)
	}()

	start := time.Now()

	origKey, err := hex.DecodeString("f07d23882e75f43cbc75b5d955a5838697292d39743d32f8fb1d8fe224d8afd5")
	if err != nil {
		panic(err)
	}

	encKey := make([]byte, 32)
	encKey[0] = 1
	copy(encKey[1:], origKey[:31])

	fmt.Println("Key:", encKey)

	numCPU := runtime.NumCPU()
	chunksPerCore, remainingChunks := divmod(maxValue, uint64(numCPU))

	fmt.Println("maxValue:", maxValue, " chunksPerCore:", chunksPerCore, " remainingChunks:", remainingChunks)

	//คำนวณจำนวน Bucket สูงสุด ที่ต้องใช้ โดยประมาณจากสูตรการคํานวณ (1<<(k+kExtraBits) / kBC)+1
	//หาก BucketCount มีเศษ(remain) ให้ใช้ BucketCount+1 เพื่อให้อยู่ใน range ของ YBucket ทั้งหมด
	BucketCount, remain := divmod(uint64(1)<<uint64(k+int(kExtraBits)), kBC)
	if remain != 0 {
		BucketCount = BucketCount + 1
	}
	//เมื่อรู้ BucketCount สูงสุดแล้ว จะสามารถคำนวณ EntrySize ของแต่ละ Bucket ได้
	//นี่เป็นการคำนวณแบบเฉลี่ย เราไม่สามารถคำนวณจำนวณ EntrySize ของแต่ละ Bucketได้
	//แต่เราสามารถคำนวณแบบค่าเฉลี่ยได้
	//เมื่อรู้ค่าเฉลี่ยของ EntrySize ของแต่ละ Bucket เราจึงสามารถนำไปใช้คำนวณ Memory Size ที่ต้องใช้ต่อ Bucket ได้ (OneBucketMemSize)
	BucketEntrySize, remain := divmod(maxValue, BucketCount)
	if remain != 0 {
		BucketEntrySize = BucketEntrySize + 1
	}
	fmt.Println("BucketCount:", BucketCount, "Bucket Entry Size:", BucketEntrySize)

	YXNumByte := cdiv(k + int(kExtraBits) + k) //คำนวณจำนวณ Byte ที่ต้องใช้เก็บผลลัพธ์ของ 1 Entry YX ในฟังก์ชั่น F1
	fmt.Println("YXNumByte", YXNumByte, "Bytes")

	OneBucketMemSize := BucketEntrySize * uint64(YXNumByte) //ใน 1 Bucket จะต้องใช้ Memory เท่าไหร่
	MemorySizeByte := 1000 * 1000000                        //(MB*Byte) ต้องการใช้ Memory ทั้งหมดเท่าไหร่ ใน 1 TmpFile

	NumBucketFitInMemory, remain := divmod(uint64(MemorySizeByte), OneBucketMemSize) //จาก MemorySizeByte จะสามารถใส่ได้กี่ Buckets ใน 1 TmpFile
	if remain != 0 {
		NumBucketFitInMemory = NumBucketFitInMemory + 1
	}

	TmpFileCount, remain := divmod(BucketCount, NumBucketFitInMemory) // ต้องใช้ทั้งหมด กี่ TmpFile
	if remain != 0 {
		TmpFileCount = TmpFileCount + 1
	}

	buffSize := int((100 * 1000000) / TmpFileCount) // กำหนด buffered writer หาร TmpFileCount

	fmt.Println("OneBucketMemSize", OneBucketMemSize, "Byte | MemorySize", MemorySizeByte/1000000, "MB | NumBucketFitInMemory/PerTmpFile:", NumBucketFitInMemory, " | TmpFileCount:", TmpFileCount)

	var ranges []Range
	var fileObjects []*bufio.Writer // Create a list to store file objects bufio.Writer
	var files []*os.File            // Create a list to store file objects os.File

	for i := uint64(0); i < TmpFileCount; i++ {
		if i == TmpFileCount-1 { //last End = BucketCount
			CreateRange := Range{
				Start: i * NumBucketFitInMemory,
				End:   BucketCount,
			}

			ranges = append(ranges, CreateRange)

			fileName := fmt.Sprintf("E://output/Bucket_%d.tmp", i)
			file, fileErr := os.Create(fileName)
			if fileErr != nil {
				fmt.Println("Error creating file:", fileErr)
				return
			}

			RangeBuff := bufio.NewWriterSize(file, buffSize) // Create a buffered writer with a larger buffer size

			files = append(files, file)
			fileObjects = append(fileObjects, RangeBuff)
		} else {
			CreateRange := Range{
				Start: i * NumBucketFitInMemory,
				End:   ((i + 1) * NumBucketFitInMemory) - 1,
			}

			ranges = append(ranges, CreateRange)

			fileName := fmt.Sprintf("E://output/Bucket_%d.tmp", i)
			file, fileErr := os.Create(fileName)
			if fileErr != nil {
				fmt.Println("Error creating file:", fileErr)
				return
			}
			RangeBuff := bufio.NewWriterSize(file, buffSize) // Create a buffered writer with a larger buffer size
			files = append(files, file)
			fileObjects = append(fileObjects, RangeBuff)
		}
	}

	fmt.Println("")
	for i, r := range ranges {
		fmt.Println("TmpFile No.", i+1, "buckets range: >=", r.Start, "<=", r.End, "| Count:", r.End-r.Start+1, "Buckets")
	}
	fmt.Println("")
	fmt.Println("Start F1 Generating...")
	var wg sync.WaitGroup
	// Setup ChaCha8 context with zero-filled IV
	chacha8Keysetup(&ctx, encKey, 256, nil)
	waitingRoomEntries := make(chan []F1Entry, 5) //สร้าง channel พร้อม buffer เพื่อรับค่า ชุด []F1Entry จาก Go F1
	// The max value our input (x), can take. A proof of space is 64 of these x values.
	// max_q := (max_value * k) / 512
	// Since k < block_size_bits, we can fit several k bit blocks into one ChaCha8 block.
	EntriesCount := uint64(0)
	if maxValue*k < uint64(kF1BlockSizeBits) {
		//ถ้า (maxValue ของ X * 512bits) น้อยกว่า 512bits  เรียก f1 แค่ครั้งเดียวพอ เพราะ 1 block ของ Chacha8 = 512bits ซึ่งสามารถ gen f1 ได้ครบอยู่แล้ว
		go f1(ranges, k, 0, maxValue, waitingRoomEntries, &wg)
		EntriesCount = maxValue
	} else {
		for i := uint64(0); i < uint64(numCPU); i++ {
			//func f1(ranges []Range, k int, start uint64, end uint64, waitingRoomEntries chan []F1Entry, wg *sync.WaitGroup)
			wg.Add(1)
			if i == uint64(numCPU-1) {
				f1Start := i * chunksPerCore
				f1End := (((i + 1) * chunksPerCore) + remainingChunks) - 1
				//เราจะเพิ่ม remainingChunks หรือเศษของ x ที่เหลือจากการหาร chunksPerCore เข้าไปใน goroutine สุดท้าย
				go f1(ranges, k, f1Start, f1End, waitingRoomEntries, &wg)
				fmt.Println("f1 CPU:", i, "X:", f1Start, "-", f1End, "Total:", (f1End-f1Start)+1, "entries")
				EntriesCount = EntriesCount + (f1End - f1Start) + 1
				break
			} else {
				f1Start := i * chunksPerCore
				f1End := ((i + 1) * chunksPerCore) - 1
				go f1(ranges, k, f1Start, f1End, waitingRoomEntries, &wg)
				fmt.Println("f1 CPU:", i, "X:", f1Start, "-", f1End, "Total:", (f1End-f1Start)+1, "entries")
				EntriesCount = EntriesCount + (f1End - f1Start) + 1
			}
			time.Sleep(200 * time.Millisecond)
		}
	}
	if maxValue != EntriesCount {
		fmt.Println("maxValue != EntriesCount")
		return
	}
	fmt.Println("[EntriesCount and MaxValue] =", EntriesCount)
	fmt.Println("")

	lastPrintedPercent := 0 // Initialize with a value outside the valid range
	count := uint64(0)
	for {
		select {
		case data := <-waitingRoomEntries:
			for _, datum := range data {
				_, err = fileObjects[datum.BucketIndex].Write(datum.xy[:])
				if err != nil {
					fmt.Println("Error writing to file:", err)
					return
				}
			}
			count += uint64(len(data))
			for _, object := range fileObjects { // Check if the buffer needs flushing
				if object.Buffered() >= buffSize {
					err = object.Flush()
					if err != nil {
						return
					}
				}
			}

			percent := calculatePercent(float64(count), float64(maxValue))
			intPercent := int(percent)
			remainder := intPercent % 1
			if remainder == 0 && intPercent != lastPrintedPercent {
				fmt.Printf("%d %d %d%% %d\n", count, maxValue, intPercent, len(waitingRoomEntries))
				lastPrintedPercent = intPercent
			}
		}
		if count == maxValue {
			fmt.Println("break")
			break
		}
	}

	for i, object := range fileObjects { // Check if the buffer needs flushing
		err = object.Flush()
		if err != nil {
			fmt.Println(err)
		}
		err = files[i].Close()
		if err != nil {
			fmt.Println(err)
		}
	}

	fmt.Println("")
	fmt.Println("")

	wg.Wait()
	close(waitingRoomEntries)

	fmt.Println("maxValue :", maxValue, " count:", count)
	fmt.Println("")
	fmt.Println("")
	timeElapsed := time.Since(start)

	fmt.Println("Computing table ", 1)
	fmt.Printf("F1 plotEntries : %d maxValue(%d) time took %s\n", len(plot.t1), maxValue, timeElapsed)
	fmt.Println("")

	// Manually trigger garbage collector
	var m runtime.MemStats
	runtime.GC()
	runtime.ReadMemStats(&m)
	fmt.Println("HeapAlloc: ", m.HeapAlloc)
	fmt.Println("HeapIdle: ", m.HeapIdle)
	fmt.Println("HeapReleased: ", m.HeapReleased)
	fmt.Println("NumGC: ", m.NumGC)
	fmt.Println("-----------")
	time.Sleep(60 * time.Second)
	for t := 1; t < 7; t++ {
		computTables(maxValue, TmpFileCount, BucketCount, k, uint8(t))
		/*		startload := time.Now()
				fmt.Println("Start runtime.GC()")
				// Manually trigger garbage collector
				runtime.GC()
				var m runtime.MemStats
				runtime.ReadMemStats(&m)
				fmt.Println("HeapAlloc: ", m.HeapAlloc)
				fmt.Println("HeapIdle: ", m.HeapIdle)
				fmt.Println("HeapReleased: ", m.HeapReleased)
				fmt.Println("NumGC: ", m.NumGC)
				timeElapsed = time.Since(startload)
				fmt.Println("END runtime.GC() time took ", timeElapsed)
				time.Sleep(600 * time.Second)*/
		fmt.Println("")
		//break //computTables 2 only
	}

	//Gen Id for Table 7
	for i := range plot.t7 {
		Ybyte, _ := PedingBits(bitarray.NewFromInt(big.NewInt(int64(i)))).Bytes()
		plot.t7[i].id = Ybyte
	}

	fmt.Println("plot.t1:", len(plot.t1))
	fmt.Println("plot.t2:", len(plot.t2))
	fmt.Println("plot.t3:", len(plot.t3))
	fmt.Println("plot.t4:", len(plot.t4))
	fmt.Println("plot.t5:", len(plot.t5))
	fmt.Println("plot.t6:", len(plot.t6))
	fmt.Println("plot.t7:", len(plot.t7))
	fmt.Println(" ")

	fmt.Println("GetQualitiesForChallenge")
	/*
		for {
			challenge, _ := hex.DecodeString("e59031d7e1ea9166bf9de3b848dd907d95dbeccda36057dac3fcd3a87e3bbb3a")
			//challenge, _ := RandomByteArray(32)
			challenge_f7 := bitarray.NewFromBytes(challenge, 0, 256).Slice(0, k).ToUint64()
			last_5_bits := bitarray.NewFromBytes(challenge, 0, 256).Slice(256-5, 256)
			fmt.Println("challenge:", bitarray.NewFromBytes(challenge, 0, 256).Slice(0, k), challenge_f7, bitarray.NewFromBytes(challenge, 0, 256), last_5_bits.ToUint64(), last_5_bits)
			for _, entry := range plot.t7 {
				f7 := new(big.Int).SetBytes(entry.y).Uint64()
				if f7 == challenge_f7 {
					fmt.Println("challenge:", ByteToHexString(challenge), "found! in F7 (Table7)", f7, "|", challenge_f7)
					E_id := new(big.Int).SetBytes(entry.id).Uint64()
					E_y := new(big.Int).SetBytes(entry.y).Uint64()
					E_x := new(big.Int).SetBytes(entry.metadata).Uint64()
					E_LID := new(big.Int).SetBytes(entry.lid).Uint64()
					E_RID := new(big.Int).SetBytes(entry.rid).Uint64()
					fmt.Println("t7 : E_id", E_id, "E_Y", E_y, "E_X:", E_x, "E_LID:", E_LID, "E_RID:", E_RID)

					//get all 64 x value
					//this is proof(xs) in proof ordering
					xs := GetInputs(new(big.Int).SetBytes(entry.id).Uint64(), 7, k)
					var proof *bitarray.BitArray
					for _, x := range xs {
						proof = proof.Append(x)
					}
					proofByte, _ := PedingBits(proof).Bytes()
					fmt.Println("proof.String(): ", proof.String())
					fmt.Println("proof.Hex(): ", ByteToHexString(proofByte))
					// Gets the quality string from a proof in proof ordering. The quality string is two
					// adjacent values, determined by the quality index (1-32), and the proof in plot
					// ordering.
					plotorderingProof := ProofToPlot(proof, uint8(k))
					QualityStringBits := GetQualityString(uint8(k), proof, last_5_bits, challenge)
					fmt.Println("Plotordering Proof : ", plotorderingProof)
					fmt.Println("QualityString Bits : ", QualityStringBits)

					PlotToProoft := PlotToProof(plotorderingProof, uint8(k))
					fmt.Println("Proofordering Proof : ", PlotToProoft)

					fmt.Println("-------------------------------------------------------------------")
				}
			}
			fmt.Println("")
			break
		}*/

}
