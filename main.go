package main

import (
	"bufio"
	"crypto/rand"
	"crypto/sha256"
	"encoding/binary"
	"encoding/hex"
	"fmt"
	"github.com/tunabay/go-bitarray"
	"log"
	"lukechampine.com/blake3"
	"math/big"
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
type ComputePlotEntry struct {
	y        []byte
	x        []byte
	xlxr     []byte
	PosL     uint64
	PosR     uint64
	isSwitch bool
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
	sigma                = "expand 32-byte k"
	tau                  = "expand 16-byte k"
	k                    = 20
	kSize                = k
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
func parallelMergeSort(plotEntries []ComputePlotEntry, numGoroutines int) {
	var wg sync.WaitGroup
	wg.Add(1)
	mergeSort(plotEntries, numGoroutines, &wg)
	wg.Wait()
}
func mergeSort(plotEntries []ComputePlotEntry, numGoroutines int, wg *sync.WaitGroup) {
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
func merge(plotEntries []ComputePlotEntry) {
	n := len(plotEntries)
	mid := n / 2

	i, j := 0, mid
	temp := make([]ComputePlotEntry, 0, n)
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
func calbucket(left ComputePlotEntry, right ComputePlotEntry, tableIndex int, metadataSize int, k int) (f, c *bitarray.BitArray) {

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
func findMatches(matchingShiftsC [][]int, bucketL []ComputePlotEntry, bucketR []ComputePlotEntry) [][]int {
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
func parallelBucketInsert(buckets map[uint32][]ComputePlotEntry, data []byte, table_index uint8, metadataSize int) {
	YXNumByte := 0
	if table_index == 1 {
		YXNumByte = cdiv(k + int(kExtraBits) + k)

		allEntries := len(data) / YXNumByte

		numCPU := runtime.NumCPU()
		chunkSize := (allEntries + numCPU - 1) / numCPU
		if chunkSize > allEntries {
			chunkSize = allEntries
		}
		//fmt.Println(maxValue, "Start LoadFile to []PlotEntry")
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
				localBuckets := make(map[uint32][]ComputePlotEntry)
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
					yStartBits := entryBitArray.Len() - (k + int(kExtraBits) + k)
					yBitsLens := k + int(kExtraBits)
					y = PedingBits(entryBitArray.Slice(yStartBits, yStartBits+yBitsLens))
					x = PedingBits(entryBitArray.Slice(entryBitArray.Len()-k, entryBitArray.Len()))
					bucketID = uint32(BucketID(y.ToUint64()))

					if _, ok := localBuckets[bucketID]; !ok {
						localBuckets[bucketID] = make([]ComputePlotEntry, 0, 1) // Adjust the initial capacity as needed
					}
					yByte, _ = PedingBits(y).Bytes()
					xByte, _ = PedingBits(x).Bytes()
					newEntry := ComputePlotEntry{
						y:        yByte,
						x:        xByte,
						xlxr:     nil,
						PosL:     0,
						PosR:     0,
						isSwitch: false,
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
	} else {
		yByteSize := cdiv(k + int(kExtraBits))
		xByteSize := cdiv(metadataSize)
		xlxrByteSize := cdiv(k)
		PosLByteSize := 4
		PosRByteSize := 4
		EntryByteSize := yByteSize + xByteSize + xlxrByteSize + PosLByteSize + PosRByteSize

		allEntries := len(data) / EntryByteSize

		numCPU := runtime.NumCPU()
		chunkSize := (allEntries + numCPU - 1) / numCPU
		if chunkSize > allEntries {
			chunkSize = allEntries
		}
		//fmt.Println(maxValue, "Start LoadFile to []PlotEntry")
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
				localBuckets := make(map[uint32][]ComputePlotEntry)
				var bucketID uint32

				var yByte []byte
				var xByte []byte
				var xlxr []byte

				for i := startIndex; i < endIndex; i++ {
					if i >= maxValue {
						break
					}
					startByte = int(i) * EntryByteSize
					byteEntry := data[startByte : startByte+EntryByteSize]

					yByte = byteEntry[0:yByteSize]
					xByte = byteEntry[yByteSize:(yByteSize + xByteSize)]
					xlxr = byteEntry[(yByteSize + xByteSize):(yByteSize + xByteSize + xlxrByteSize)]
					BytePosL := byteEntry[(yByteSize + xByteSize + xlxrByteSize):(yByteSize + xByteSize + xlxrByteSize + PosLByteSize)]
					BytePosR := byteEntry[(yByteSize + xByteSize + xlxrByteSize + PosLByteSize):EntryByteSize]

					y := bitarray.NewBufferFromByteSlice(yByte).BitArray().ToUint64()
					PosL := bitarray.NewBufferFromByteSlice(BytePosL).BitArray().ToUint64()
					PosR := bitarray.NewBufferFromByteSlice(BytePosR).BitArray().ToUint64()
					bucketID = uint32(BucketID(y))

					if _, ok := localBuckets[bucketID]; !ok {
						localBuckets[bucketID] = make([]ComputePlotEntry, 0, 1) // Adjust the initial capacity as needed
					}

					newEntry := ComputePlotEntry{
						y:        yByte,
						x:        xByte,
						xlxr:     xlxr,
						PosL:     PosL,
						PosR:     PosR,
						isSwitch: false,
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

}
func parallelMergeSortBuckets(buckets map[uint32][]ComputePlotEntry, numCPU int) {
	sem := make(chan struct{}, numCPU)
	var wg sync.WaitGroup
	wg.Add(len(buckets))

	for _, entries := range buckets {
		sem <- struct{}{} // Acquire semaphore
		go func(entries []ComputePlotEntry) {
			defer func() { <-sem }() // Release semaphore
			defer wg.Done()
			parallelMergeSort(entries, numCPU)
		}(entries)
	}

	wg.Wait()
}
func loadDataFromFile(filename string, table_index uint8, metadataSize int) (map[uint32][]ComputePlotEntry, error) {
	buckets := make(map[uint32][]ComputePlotEntry)
	startTimeReadFile := time.Now()
	fmt.Println(filename, "ReadFile ")
	data, err := os.ReadFile(filename)
	if err != nil {
		fmt.Println(err)
	}
	timeElapsed := time.Since(startTimeReadFile)
	fmt.Println(filename, "End ReadFile", len(data), "time took ", timeElapsed)

	parallelBucketInsert(buckets, data, table_index, metadataSize)

	fmt.Println(filename, "Start parallelMergeSortBuckets:", len(buckets))
	startTimeReadFile = time.Now()
	parallelMergeSortBuckets(buckets, runtime.NumCPU())
	timeElapsed = time.Since(startTimeReadFile)
	fmt.Println(filename, "End parallelMergeSortBuckets:", len(buckets), "time took ", timeElapsed)
	//runtime.GC()
	return buckets, nil
}
func GoMatchingAndCalculateFx(b uint32, matchingShiftsC [][]int, tableIndex uint8, metadataSize int, leftBucket, rightBucket []ComputePlotEntry, wg1 *sync.WaitGroup, goroutineSem chan struct{}, matchResult chan map[int]FxMatched) {
	//start := time.Now()
	defer wg1.Done()
	m := 0

	Matches := findMatches(matchingShiftsC, leftBucket, rightBucket)
	NewEntries := make([]ComputePlotEntry, 0)
	for _, match := range Matches {
		L_Entry := leftBucket[match[0]]
		R_Entry := rightBucket[match[1]]
		f, c := calbucket(L_Entry, R_Entry, int(tableIndex+1), metadataSize, k)
		Fx, _ := PedingBits(f).Bytes()
		C, _ := PedingBits(c).Bytes()

		var bitsXL *bitarray.BitArray
		var bitsXR *bitarray.BitArray
		var LXL []*bitarray.BitArray
		var RXL []*bitarray.BitArray
		var newxlxr *bitarray.BitArray
		var isSwitch bool
		if tableIndex+1 == 2 {
			bitsXL = NewBits(new(big.Int).SetBytes(L_Entry.x[:]), k)
			bitsXR = NewBits(new(big.Int).SetBytes(R_Entry.x[:]), k)
		} else {
			bitsXL = NewBits(new(big.Int).SetBytes(L_Entry.xlxr), k)
			bitsXR = NewBits(new(big.Int).SetBytes(R_Entry.xlxr), k)

			if bitsXL.Equal(bitsXR) {
				LXL = GetInputs(L_Entry.PosL, L_Entry.PosR, tableIndex-1)
				RXL = GetInputs(R_Entry.PosL, R_Entry.PosR, tableIndex-1)
				bitsXL = bitarray.MustParse("")
				bitsXR = bitarray.MustParse("")
				for _, value := range LXL {
					bitsXL = bitsXL.Append(value)
				}
				for _, value := range RXL {
					bitsXR = bitsXR.Append(value)
				}
			}
		}
		Compare := CompareProofBits(bitsXL, bitsXR, uint8(k))
		if Compare == 1 { //switch
			if bitsXL.Len() > k {
				newxlxr = LXL[len(LXL)-1] //ดึงชุดสุดท้ายมา
			} else {
				newxlxr = bitsXL
			}
			isSwitch = true
		} else if Compare == 0 { //switch
			if bitsXL.Len() > k {
				newxlxr = LXL[len(LXL)-1]
			} else {
				newxlxr = bitsXL
			}
			isSwitch = true
		} else if Compare == -1 {
			if bitsXR.Len() > k {
				newxlxr = RXL[len(RXL)-1]
			} else {
				newxlxr = bitsXR
			}
			isSwitch = false
		}

		Bytesxlxr, _ := PedingBits(newxlxr).Bytes()

		if tableIndex+1 == 7 {
			f7, _ := PedingBits(f.Slice(0, k)).Bytes()
			newEntry := ComputePlotEntry{
				y:        f7,
				PosL:     0,
				PosR:     0,
				isSwitch: isSwitch,
			}
			NewEntries = append(NewEntries, newEntry)
		} else {
			newEntry := ComputePlotEntry{
				y:        Fx,
				x:        C,
				xlxr:     Bytesxlxr,
				PosL:     0,
				PosR:     0,
				isSwitch: isSwitch,
			}
			NewEntries = append(NewEntries, newEntry)
		}
		m++
	}

	res := make(map[int]FxMatched)
	res[int(b)] = FxMatched{
		MatchPos: Matches,
		BucketL:  leftBucket,
		Output:   NewEntries,
	}
	//timeElapsed := time.Since(start)
	//fmt.Printf("%d %d %d %d \n", b, len(leftBucket), len(rightBucket), m)
	matchResult <- res
	<-goroutineSem
}
func GetInputs(PosL uint64, PosR uint64, tableIndex uint8) []*bitarray.BitArray {
	fileName := fmt.Sprintf("E://output/Table%d.tmp", tableIndex)
	data, err := os.ReadFile(fileName)
	if err != nil {
		fmt.Println(err)
	}
	XByte := 0
	var EntryL_Bitarray *bitarray.BitArray
	var EntryR_Bitarray *bitarray.BitArray
	var result []*bitarray.BitArray
	if tableIndex == 1 {
		XByte = cdiv(k)

		PosL_ReadByte := PosL * uint64(XByte)
		PosR_ReadByte := PosR * uint64(XByte)

		bitsXL := NewBits(new(big.Int).SetBytes(data[PosL_ReadByte:PosL_ReadByte+uint64(XByte)]), k)
		bitsXR := NewBits(new(big.Int).SetBytes(data[PosR_ReadByte:PosR_ReadByte+uint64(XByte)]), k)

		result = append(result, bitsXL, bitsXR)
	} else {

		PosLByteSize := 4
		PosRByteSize := 4
		EntryByteSize := PosLByteSize + PosRByteSize

		PosL_ReadByte := PosL * uint64(EntryByteSize)
		PosR_ReadByte := PosR * uint64(EntryByteSize)

		Get_PosL_BitsPos_start := 0
		Get_PosL_BitsPos_end := PosLByteSize * 8

		Get_PosR_BitsPos_start := PosLByteSize * 8
		Get_PosR_BitsPos_end := (PosRByteSize + PosRByteSize) * 8

		EntryL_Bitarray = bitarray.NewBufferFromByteSlice(data[PosL_ReadByte : PosL_ReadByte+uint64(EntryByteSize)]).BitArray()
		EntryR_Bitarray = bitarray.NewBufferFromByteSlice(data[PosR_ReadByte : PosR_ReadByte+uint64(EntryByteSize)]).BitArray()

		L_PosL := EntryL_Bitarray.Slice(Get_PosL_BitsPos_start, Get_PosL_BitsPos_end).ToUint64()
		L_PosR := EntryL_Bitarray.Slice(Get_PosR_BitsPos_start, Get_PosR_BitsPos_end).ToUint64()

		R_PosL := EntryR_Bitarray.Slice(Get_PosL_BitsPos_start, Get_PosL_BitsPos_end).ToUint64()
		R_PosR := EntryR_Bitarray.Slice(Get_PosR_BitsPos_start, Get_PosR_BitsPos_end).ToUint64()

		L_xlxr := GetInputs(L_PosL, L_PosR, tableIndex-1)
		R_xlxr := GetInputs(R_PosL, R_PosR, tableIndex-1)

		result = append(L_xlxr, R_xlxr...)

	}
	return result //return l+r
}

type FxFandC struct {
	F *bitarray.BitArray
	C *bitarray.BitArray
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
func f1N(k int, x uint64) ComputePlotEntry {

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

		newEntry := ComputePlotEntry{
			y: Ybyte,
			x: Xbyte,
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

		newEntry := ComputePlotEntry{
			y: Ybyte,
			x: Xbyte,
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

/*
func GetInputs(id uint64, table_index uint8, k int) []*bitarray.BitArray {

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
*/
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

func PlotToProof(proof *bitarray.BitArray, k uint8) *bitarray.BitArray {
	// Calculates f1 for each of the inputs

	var results []ComputePlotEntry
	var xs *bitarray.BitArray
	for i := 0; i < 64; i++ {
		x := proof.Slice(i*int(k), (i+1)*int(k)).ToUint64()
		result := f1N(int(k), x)
		results = append(results, result)
		xs = xs.Append(PedingBitsWithlen(bitarray.NewBufferFromByteSlice(result.x).BitArray(), int(k)))
		//fmt.Println("xs:", PedingBitsWithlen(bitarray.NewBufferFromByteSlice(result.y).BitArray(), uint64(k+6)))
	}

	// The plotter calculates f1..f7, and at each level, decides to swap or not swap. Here, we
	// are doing a similar thing, we swap left and right, such that we end up with proof
	// ordering.
	for tableIndex := uint8(2); tableIndex < 8; tableIndex++ {
		metadataSize := int(kVectorLens[tableIndex] * k) //0, 0, 1, 2, 4, 4, 3, 2
		var newXs *bitarray.BitArray
		var newResults []ComputePlotEntry
		// Computes the output pair (fx, new_metadata)
		//fmt.Println("tableIndex :", tableIndex)
		// Iterates through pairs of things, starts with 64 things, then 32, etc, up to 2.
		for i := 0; i < len(results); i += 2 {
			var newOutput ComputePlotEntry
			var Fx []byte
			var C []byte

			// Compares the buckets of both ys to see which one goes on the left and which one goes on the right
			if bitarray.NewBufferFromByteSlice(results[i].y).Uint64() < bitarray.NewBufferFromByteSlice(results[i+1].y).Uint64() {
				FxOutput, COutput := calbucket(
					results[i],
					results[i+1],
					int(tableIndex),
					metadataSize,
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
					int(tableIndex),
					metadataSize,
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

			newOutput = ComputePlotEntry{
				y: Fx,
				x: C,
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

func computTables(BucketCount uint64, k int, table_index uint8, NumBucketFitInMemory, TmpFileCount uint64) {
	start := time.Now()
	metadataSize := int(kVectorLens[table_index+1]) * k //0, 0, 1, 2, 4, 4, 3, 2

	// Precomputation necessary to compute matches
	matchingShiftsC := make([][]int, 2)
	for i := 0; i < 2; i++ {
		matchingShiftsC[i] = make([]int, kExtraBitsPow)
	}
	for parity := 0; parity < 2; parity++ {
		for r := int64(0); r < kExtraBitsPow; r++ {
			v := ((2*r + int64(parity)) * (2*r + int64(parity))) % kCInt64
			matchingShiftsC[parity][r] = int(v)
		}
	}

	fmt.Println("Computing table ", table_index+1)
	var wg sync.WaitGroup
	numCPU := runtime.NumCPU()
	entryCount := 0

	FirstLoad := true
	NeedLoad := false
	LoopTmpFile := uint64(0)
	bucketsContinue := make([]ComputePlotEntry, 0, 1) // Adjust the initial capacity as needed

	buckets := make(map[uint32][]ComputePlotEntry)
	var err error
	wg.Add(1)
	matchResult := make(chan map[int]FxMatched, numCPU)
	go func(wg *sync.WaitGroup) {
		defer wg.Done()
		var wg1 sync.WaitGroup
		goroutineSem := make(chan struct{}, numCPU)
		for b := uint32(0); b < uint32(BucketCount-1); b++ { //BucketCount-1 เพรา bucket เป็นคู่สุดท้าย เช่น มี4 bucket = 1-2,2-3,3-4
			if NeedLoad == true || FirstLoad == true {
				startload := time.Now()
				fileName := fmt.Sprintf("E://output/table_%d_Bucket_%d.tmp", table_index, LoopTmpFile)
				buckets = make(map[uint32][]ComputePlotEntry)
				buckets, err = loadDataFromFile(fileName, table_index, metadataSize)
				if err != nil {
					fmt.Println("err loadDataFromFile:", err)
				}

				if NeedLoad == true {
					buckets[b] = bucketsContinue
					bucketsContinue = make([]ComputePlotEntry, 0, 1) // Adjust the initial capacity as needed
					fmt.Println(fileName, "buckets NeedLoad at:", b+1, len(buckets[b]))
					NeedLoad = false
				}

				timeElapsed := time.Since(startload)
				fmt.Println(fileName, "LoadData time took ", timeElapsed)

				LoopTmpFile++
				FirstLoad = false
				e := os.Remove(fileName)
				if e != nil {
					log.Fatal(e)
				}
				fmt.Println(fileName, "Find Matching... buckets : ", len(buckets))
				fmt.Println("")

			}
			if len(buckets[b+1]) == 0 {
				fmt.Println("R buckets Continue at:", b+1, len(bucketsContinue))
				bucketsContinue = buckets[b]
				fmt.Println("create bucketsContinue:", b)
				b--
				fmt.Println("Backward loop 1 step to :", b)
				NeedLoad = true
				fmt.Println("Set NeedLoad :", NeedLoad)
				continue
			}

			entryCount += len(buckets[b])
			wg1.Add(1)
			goroutineSem <- struct{}{}
			go GoMatchingAndCalculateFx(b, matchingShiftsC, table_index, metadataSize, buckets[b], buckets[b+1], &wg1, goroutineSem, matchResult)
		}
		wg1.Wait()
	}(&wg)

	current := 0

	currentTableTempSlot := make(map[int]FxMatched)

	CurrentHashmap := make(map[int]uint64) //old pos,new pos
	NexttHashmap := make(map[int]uint64)   //old pos,new pos

	HashmapCount := 0

	OutputPlotEntryL := make([]ComputePlotEntry, 0, 1) // Adjust the initial capacity as needed
	OutputPlotEntryR := make([]ComputePlotEntry, 0, 1) // Adjust the initial capacity as needed

	CurrentSlot := FxMatched{}
	NexttSlot := FxMatched{}

	fileName := fmt.Sprintf("E://output/Table%d.tmp", table_index)
	file, fileErr := os.Create(fileName)
	if fileErr != nil {
		fmt.Println("Error creating file:", fileErr)
		return
	}
	buffSize := 5 * 1000000                            // กำหนด buffered writer
	WriteBuffer := bufio.NewWriterSize(file, buffSize) // Create a buffered writer with a larger buffer size

	var objfileObjects []*bufio.Writer // Create a list to store file objects bufio.Writer
	var objfiles []*os.File            // Create a list to store file objects os.File
	var ranges []Range
	if table_index+1 != 7 {
		for i := uint64(0); i < TmpFileCount; i++ {
			if i == TmpFileCount-1 { //last End = BucketCount
				CreateRange := Range{
					Start: i * NumBucketFitInMemory,
					End:   BucketCount,
				}

				ranges = append(ranges, CreateRange)

				objfileName := fmt.Sprintf("E://output/table_%d_Bucket_%d.tmp", table_index+1, i)
				objfile, objfileErr := os.Create(objfileName)
				if objfileErr != nil {
					fmt.Println("Error creating file:", objfileErr)
					return
				}

				RangeBuff := bufio.NewWriterSize(objfile, buffSize) // Create a buffered writer with a larger buffer size

				objfiles = append(objfiles, objfile)
				objfileObjects = append(objfileObjects, RangeBuff)
			} else {
				CreateRange := Range{
					Start: i * NumBucketFitInMemory,
					End:   ((i + 1) * NumBucketFitInMemory) - 1,
				}

				ranges = append(ranges, CreateRange)

				objfileName := fmt.Sprintf("E://output/table_%d_Bucket_%d.tmp", table_index+1, i)
				objfile, objfileErr := os.Create(objfileName)
				if objfileErr != nil {
					fmt.Println("Error creating file:", objfileErr)
					return
				}
				RangeBuff := bufio.NewWriterSize(objfile, buffSize) // Create a buffered writer with a larger buffer size
				objfiles = append(objfiles, objfile)
				objfileObjects = append(objfileObjects, RangeBuff)
			}
		}
	}
	F7fileName := fmt.Sprintf("E://output/Table%d.tmp", table_index+1)
	F7file, F7fileErr := os.Create(F7fileName)
	if F7fileErr != nil {
		fmt.Println("Error creating file:", F7fileErr)
		return
	}
	// กำหนด buffered writer
	F7WriteBuffer := bufio.NewWriterSize(F7file, buffSize)

	for {
		if len(CurrentSlot.MatchPos) == 0 { //เช็ค CurrentSlot ว่ามีของยัง?, use only init CurrentSlot
			for {
				_, ok := currentTableTempSlot[current] // ถ้าไม่มีให้ไปเช็คที่ TempSlot, current = 0 init
				if ok {
					CurrentSlot = currentTableTempSlot[current] //ถ้ามีก็โยนของเข้า CurrentSlot
					delete(currentTableTempSlot, current)       //แล้วลบออกจาก TempSlot

					for _, pos := range CurrentSlot.MatchPos { // เพิ่ม L Pos Matched เข้าไปที่ CurrentHashmap
						_, ok = CurrentHashmap[pos[0]]
						if !ok {
							//CurrentHashmap [pos L เก่า][Pos L ใหม่]
							//HashmapCount คือ New Pos ของ ตาราง L
							CurrentHashmap[pos[0]] = uint64(HashmapCount) //โยน pos เข้าไปที่ hashmap พร้อม value ของ new pos
							HashmapCount++
						}
					}
					//เลือก entry ที่ใช้ OutputPlotEntryL
					//Select used Entry and append to CurrentOut, aka create new CurrentOut from CurrentHashmap
					//88888888888888888888888888888888888888888888888888888888888888888888888888888
					// Create slice of key-value pairs
					pairs := make([][2]interface{}, 0, len(CurrentHashmap))

					for key, v := range CurrentHashmap {
						pairs = append(pairs, [2]interface{}{key, v})
					}

					// Sort slice based on values
					sort.Slice(pairs, func(i, j int) bool {
						return pairs[i][1].(uint64) < pairs[j][1].(uint64)
					})

					// Extract sorted keys
					keys := make([]int, len(pairs))
					for i, p := range pairs {
						keys[i] = p[0].(int)
					}
					// use sorted map
					for _, key := range keys {
						SelectedEntry := CurrentSlot.BucketL[key] // ถูกแล้ว
						OutputPlotEntryL = append(OutputPlotEntryL, SelectedEntry)
					}
					//88888888888888888888888888888888888888888888888888888888888888888888888888888
					break
				} else {
					data := <-matchResult
					for key, value := range data {
						currentTableTempSlot[key] = value
					}
				}
			}
		}

		if len(NexttSlot.MatchPos) == 0 {
			for {
				_, ok := currentTableTempSlot[current+1] // current = 0 init
				if ok {
					NexttSlot = currentTableTempSlot[current+1]
					delete(currentTableTempSlot, current+1) //แล้วลบออกจาก TempSlot
					break
				} else {
					data := <-matchResult
					for key, value := range data {
						currentTableTempSlot[key] = value
					}
				}
			}
		}

		//create NexttHashmap from Current matches R
		for _, pos := range CurrentSlot.MatchPos {
			_, ok := NexttHashmap[pos[1]]
			if !ok {
				NexttHashmap[pos[1]] = uint64(HashmapCount) //โยน pos เข้าไปที่ hashmap พร้อม value ของ new pos
				HashmapCount++
			}
		}
		//fmt.Println("#########################################")
		//create NexttHashmap from Next matches L
		for _, pos := range NexttSlot.MatchPos {
			_, ok := NexttHashmap[pos[0]]
			if !ok {
				NexttHashmap[pos[0]] = uint64(HashmapCount) //โยน pos เข้าไปที่ hashmap พร้อม value ของ new pos
				HashmapCount++
			}
		}

		OutputPlotEntryR = CurrentSlot.Output //create new NextOut from CurrentSlot

		for i, pos := range CurrentSlot.MatchPos { // ถูกแล้ว
			OutputPlotEntryR[i].PosL = CurrentHashmap[pos[0]] // ถูกแล้ว //add new PosL to NextOut
		}

		//88888888888888888888888888888888888888888888888888888888888888888888888888888
		// Create slice of key-value pairs
		Nextpairs := make([][2]interface{}, 0, len(NexttHashmap))

		for key, v := range NexttHashmap {
			Nextpairs = append(Nextpairs, [2]interface{}{key, v})
		}

		// Sort slice based on values
		sort.Slice(Nextpairs, func(i, j int) bool {
			return Nextpairs[i][1].(uint64) < Nextpairs[j][1].(uint64)
		})

		// Extract sorted keys
		Nextkeys := make([]int, len(Nextpairs))
		for i, p := range Nextpairs {
			Nextkeys[i] = p[0].(int)
		}
		// use sorted map
		for _, key := range Nextkeys {
			SelectedEntry := NexttSlot.BucketL[key] // ถูกแล้ว
			OutputPlotEntryL = append(OutputPlotEntryL, SelectedEntry)
		}
		//88888888888888888888888888888888888888888888888888888888888888888888888888888

		//parallelMergeSort(OutputPlotEntryL, 4)

		for i, v := range CurrentSlot.MatchPos { // ถูกแล้ว
			OutputPlotEntryR[i].PosR = NexttHashmap[v[1]] //add new PosR to NextOut
		}

		for i, v := range OutputPlotEntryR { // ถูกแล้ว
			if v.isSwitch == true {
				PosL := v.PosR
				PosR := v.PosL

				OutputPlotEntryR[i].PosL = PosL
				OutputPlotEntryR[i].PosR = PosR
			}
		}

		//นำไปใช้งาน
		for i := 0; i < len(OutputPlotEntryL); i++ {
			var dataWrite []byte
			if table_index == 1 {
				dataWrite = OutputPlotEntryL[i].x[:]
				_, err = WriteBuffer.Write(dataWrite) //write only X
				if err != nil {
					fmt.Println("Error writing to file:", err)
					return
				}
			} else {
				PosLByte := make([]byte, 4)
				PosRByte := make([]byte, 4)
				binary.BigEndian.PutUint32(PosLByte, uint32(OutputPlotEntryL[i].PosL))
				binary.BigEndian.PutUint32(PosRByte, uint32(OutputPlotEntryL[i].PosR))
				dataWrite = append(dataWrite, PosLByte...)
				dataWrite = append(dataWrite, PosRByte...)
				_, err = WriteBuffer.Write(dataWrite)
				if err != nil {
					fmt.Println("Error writing to file:", err)
					return
				}
			}

			if WriteBuffer.Buffered() >= buffSize {
				err = WriteBuffer.Flush()
				if err != nil {
					return
				}
			}
		}

		if table_index+1 == 7 {
			for i := 0; i < len(OutputPlotEntryR); i++ {

				var dataWrite []byte
				y := OutputPlotEntryR[i].y
				PosLByte := make([]byte, 4)
				PosRByte := make([]byte, 4)
				binary.BigEndian.PutUint32(PosLByte, uint32(OutputPlotEntryR[i].PosL))
				binary.BigEndian.PutUint32(PosRByte, uint32(OutputPlotEntryR[i].PosR))

				dataWrite = append(dataWrite, y...)
				dataWrite = append(dataWrite, PosLByte...)
				dataWrite = append(dataWrite, PosRByte...)

				_, err = F7WriteBuffer.Write(dataWrite) //write only X
				if err != nil {
					fmt.Println("Error writing to file:", err)
					return
				}
			}
		} else {
			for i := 0; i < len(OutputPlotEntryR); i++ {

				var BucketIndex int
				var dataWrite []byte

				bucketid := BucketID(new(big.Int).SetBytes(OutputPlotEntryR[i].y).Uint64())

				y := OutputPlotEntryR[i].y
				x := OutputPlotEntryR[i].x
				xlxr := OutputPlotEntryR[i].xlxr
				PosLByte := make([]byte, 4)
				PosRByte := make([]byte, 4)
				binary.BigEndian.PutUint32(PosLByte, uint32(OutputPlotEntryR[i].PosL))
				binary.BigEndian.PutUint32(PosRByte, uint32(OutputPlotEntryR[i].PosR))

				dataWrite = append(dataWrite, y...)
				dataWrite = append(dataWrite, x...)
				dataWrite = append(dataWrite, xlxr...)
				dataWrite = append(dataWrite, PosLByte...)
				dataWrite = append(dataWrite, PosRByte...)

				for index, rg := range ranges {
					if bucketid >= rg.Start && bucketid <= rg.End {
						BucketIndex = index
						break
					}
				}

				_, err = objfileObjects[BucketIndex].Write(dataWrite)
				if err != nil {
					fmt.Println("Error writing to file:", err)
					return
				}
			}
		}

		current++
		CurrentSlot = NexttSlot
		NexttSlot = FxMatched{}
		CurrentHashmap = NexttHashmap
		NexttHashmap = make(map[int]uint64)
		OutputPlotEntryR = make([]ComputePlotEntry, 0, 1)
		OutputPlotEntryL = make([]ComputePlotEntry, 0, 1)

		if uint64(current) == (BucketCount - 2) {
			break
		}

	}

	if table_index+1 != 7 {
		for i, object := range objfileObjects { // Check if the buffer needs flushing
			err = object.Flush()
			if err != nil {
				fmt.Println(err)
			}
			err = objfiles[i].Close()
			if err != nil {
				fmt.Println(err)
			}
		}
	}

	err = WriteBuffer.Flush()
	if err != nil {
		fmt.Println(err)
	}
	err = file.Close()
	if err != nil {
		return
	}

	//fmt.Println(TempSlot)
	wg.Wait()
	timeElapsed := time.Since(start)
	fmt.Printf("computTables time took %s \n", timeElapsed)
}

type FxMatched struct {
	MatchPos [][]int
	BucketL  []ComputePlotEntry
	Output   []ComputePlotEntry
}

func f1(ranges []Range, k int, start uint64, end uint64, waitingRoomEntries chan []F1Entry, wg *sync.WaitGroup) {
	defer wg.Done()
	F1NumBits := F1NumByte * 8             // แปลง F1NumByte เป็น bits
	Buffer := (10 * 1000000) / (F1NumByte) //กำหนด buffer MB และหารค่าว่าสามารถใส่ F1 ได้กี่ Entries *Buffer ในที่นี้คือจำนวน index สูงสุดของ bufferPool
	NumBlock := uint64(100000)             //จำนวน Block ที่ต้องการให้ Chacha8  gen ออกมาใน 1 ครั้ง (1block = 512bits)
	bufferPool := make([]F1Entry, Buffer)  //หลังจาก คำนวณ F1 จะเก็บไว้ในบัพเฟอร์นี้

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
	fmt.Println("K Size:", k)
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
	fmt.Println("YXNumByte", YXNumByte, "Bytes.")

	F1TableSize := maxValue * uint64(YXNumByte)
	fmt.Println("YXNumByte :", YXNumByte, "Bytes.")
	fmt.Println("F1TableSize :", F1TableSize/1000000, "MB.")

	OneBucketMemSize := BucketEntrySize * uint64(YXNumByte) //ใน 1 Bucket จะต้องใช้ Memory เท่าไหร่
	BucketSizeByte := 10 * 1000000                          //(MB*Byte) ต้องการใช้ Memory ทั้งหมดเท่าไหร่ ใน 1 TmpFile

	NumBucketFitInMemory, remain := divmod(uint64(BucketSizeByte), OneBucketMemSize) //จาก BucketSizeByte จะสามารถใส่ได้กี่ Buckets ใน 1 TmpFile
	if remain != 0 {
		NumBucketFitInMemory = NumBucketFitInMemory + 1
	}

	TmpFileCount, remain := divmod(BucketCount, NumBucketFitInMemory) // ต้องใช้ทั้งหมด กี่ TmpFile
	if remain != 0 {
		TmpFileCount = TmpFileCount + 1
	}

	buffSize := int((50 * 1000000) / TmpFileCount) // กำหนด buffered writer หาร TmpFileCount

	fmt.Println("OneBucketMemSize", OneBucketMemSize, "Byte | MemorySize", BucketSizeByte/1000000, "MB | NumBucketFitInMemory/PerTmpFile:", NumBucketFitInMemory, " | TmpFileCount:", TmpFileCount)

	var fileObjects []*bufio.Writer // Create a list to store file objects bufio.Writer
	var files []*os.File            // Create a list to store file objects os.File
	var ranges []Range
	for i := uint64(0); i < TmpFileCount; i++ {
		if i == TmpFileCount-1 { //last End = BucketCount
			CreateRange := Range{
				Start: i * NumBucketFitInMemory,
				End:   BucketCount,
			}

			ranges = append(ranges, CreateRange)

			fileName := fmt.Sprintf("E://output/table_%d_Bucket_%d.tmp", 1, i)
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

			fileName := fmt.Sprintf("E://output/table_%d_Bucket_%d.tmp", 1, i)
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

	lastPrintedPercent := -1 // Initialize with a value outside the valid range
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
			levelPercent := intPercent / 10
			if levelPercent != lastPrintedPercent {
				fmt.Printf("%d %d %d%% %d\n", count, maxValue, intPercent, len(waitingRoomEntries))
				lastPrintedPercent = levelPercent
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
	startload := time.Now()
	fmt.Println("Start runtime.GC()")
	runtime.GC()
	runtime.ReadMemStats(&m)
	fmt.Println("HeapAlloc: ", m.HeapAlloc)
	fmt.Println("HeapIdle: ", m.HeapIdle)
	fmt.Println("HeapReleased: ", m.HeapReleased)
	fmt.Println("NumGC: ", m.NumGC)
	timeElapsed = time.Since(startload)
	fmt.Println("END runtime.GC() time took ", timeElapsed)
	fmt.Println("")

	//computTables
	for t := 1; t < 7; t++ {
		computTables(BucketCount, k, uint8(t), NumBucketFitInMemory, TmpFileCount)
	}

	fmt.Println("GetQualitiesForChallenge")

	fileName := "E://output/Table7.tmp"
	fmt.Println(fileName, "ReadFile ")
	data, err := os.ReadFile(fileName)
	if err != nil {
		fmt.Println(err)
	}

	YByteLens := cdiv(k)
	PosLByteLens := 4
	PosRByteLens := 4
	F7entrySize := YByteLens + PosLByteLens + PosRByteLens

	allEntries := len(data) / F7entrySize
	fmt.Println("allEntries :", allEntries)
	hashmap_f7 := make(map[uint64]uint64) //[f7][EntryPos]

	for i := 0; i < allEntries; i++ {
		EntryByte := data[i*F7entrySize : (i+1)*F7entrySize]
		y := new(big.Int).SetBytes(EntryByte[0:YByteLens]).Uint64()
		hashmap_f7[y] = uint64(i)
	}
	fmt.Println("created hashmap_f7 :", len(hashmap_f7))

	for {
		challenge, _ := hex.DecodeString("e59031d7e1ea9166bf9de3b848dd907d95dbeccda36057dac3fcd3a87e3bbb3a")
		//challenge, _ := RandomByteArray(32)
		challenge_f7 := bitarray.NewFromBytes(challenge, 0, 256).Slice(0, k).ToUint64()
		last_5_bits := bitarray.NewFromBytes(challenge, 0, 256).Slice(256-5, 256)
		fmt.Println("challenge:", bitarray.NewFromBytes(challenge, 0, 256).Slice(0, k), challenge_f7, bitarray.NewFromBytes(challenge, 0, 256), last_5_bits.ToUint64(), last_5_bits)

		_, ok := hashmap_f7[challenge_f7]
		if !ok {
			continue
		}
		fmt.Println("challenge:", ByteToHexString(challenge), "found! in F7 (Table7)", challenge_f7)
		EntryPos := hashmap_f7[challenge_f7]
		EntryByte := data[(int(EntryPos) * F7entrySize) : (int(EntryPos)*F7entrySize)+F7entrySize]

		PosL := new(big.Int).SetBytes(EntryByte[YByteLens : YByteLens+PosLByteLens]).Uint64()
		PosR := new(big.Int).SetBytes(EntryByte[YByteLens+PosLByteLens : F7entrySize]).Uint64()

		fmt.Println("t7 : PosL", PosL, "PosR", PosR)

		//get all 64 x value
		//this is proof(xs) in proof ordering
		xs := GetInputs(PosL, PosR, 6)
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
		break
	}

}
