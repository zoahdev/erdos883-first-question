import Erdos883AdaptiveCertificate1546Data
import Erdos883AdaptiveSpanCompactCore
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
def adaptiveNumericSpans1546_0Chunk0 : List AdaptiveNumericSpan := adaptivePackedNumericSpans 10 15082811756121781043176980783689262785008219690041138754131487490551054509796400818046122466406455218028813338818121155779513711807227017811073265752193167110609435854378893991206411494281673433307901839669105461475159270281185020079878466352644100631477655610245676872707468680707812320291988701248
def adaptiveNumericSpans1546_0 : List AdaptiveNumericSpan := [adaptiveNumericSpans1546_0Chunk0].flatten
def adaptiveSpanEven1546_0 := adaptiveSpanTreeOfSpans (coreEvenSpans 773 0 adaptiveNumericSpans1546_0)
def adaptiveSpanWhole1546_0 := adaptiveSpanTreeOfSpans (coreWholeSpans 0 adaptiveNumericSpans1546_0)
theorem adaptiveSpanNumericCheck1546_0 : coreNumericSpansCheck 1509 6 480 1155 adaptiveNumericSpans1546_0 adaptiveRows1546 = true := by decide +kernel
theorem adaptiveSpanEvenCache1546_0 : adaptiveSpanEven1546_0.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain1546_0 : adaptiveSpanEven1546_0.domainCheck 773 = true := by decide +kernel
theorem adaptiveSpanEvenEntries1546_0 : adaptiveSpanEven1546_0.spans = coreEvenSpans 773 0 adaptiveNumericSpans1546_0 := by decide +kernel
theorem adaptiveSpanWholeCache1546_0 : adaptiveSpanWhole1546_0.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain1546_0 : adaptiveSpanWhole1546_0.domainCheck 773 = true := by decide +kernel
theorem adaptiveSpanWholeEntries1546_0 : adaptiveSpanWhole1546_0.spans = coreWholeSpans 0 adaptiveNumericSpans1546_0 := by decide +kernel
def adaptiveNumericSpans1546_1Chunk0 : List AdaptiveNumericSpan := adaptivePackedNumericSpans 7 7404293263029316261836352409041912948133496092645316123847043093433726955275922419207978273957964979517830458674875938539580962654226464474834235493981429595668324048030085331646749178135633316984420233642112
def adaptiveNumericSpans1546_1 : List AdaptiveNumericSpan := [adaptiveNumericSpans1546_1Chunk0].flatten
def adaptiveSpanEven1546_1 := adaptiveSpanTreeOfSpans (coreEvenSpans 773 0 adaptiveNumericSpans1546_1)
def adaptiveSpanWhole1546_1 := adaptiveSpanTreeOfSpans (coreWholeSpans 0 adaptiveNumericSpans1546_1)
theorem adaptiveSpanNumericCheck1546_1 : coreNumericSpansCheck 1509 6 240 385 adaptiveNumericSpans1546_1 adaptiveRows1546 = true := by decide +kernel
theorem adaptiveSpanEvenCache1546_1 : adaptiveSpanEven1546_1.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain1546_1 : adaptiveSpanEven1546_1.domainCheck 773 = true := by decide +kernel
theorem adaptiveSpanEvenEntries1546_1 : adaptiveSpanEven1546_1.spans = coreEvenSpans 773 0 adaptiveNumericSpans1546_1 := by decide +kernel
theorem adaptiveSpanWholeCache1546_1 : adaptiveSpanWhole1546_1.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain1546_1 : adaptiveSpanWhole1546_1.domainCheck 773 = true := by decide +kernel
theorem adaptiveSpanWholeEntries1546_1 : adaptiveSpanWhole1546_1.spans = coreWholeSpans 0 adaptiveNumericSpans1546_1 := by decide +kernel
def adaptiveNumericSpans1546_2Chunk0 : List AdaptiveNumericSpan := adaptivePackedNumericSpans 9 11898240535212346940838156209134410880353736543182533026116199825567429126672558203148578369561971466001993062610804013390325894137907990717386176435445303636326294876100441266876021671880421511476867886047510230374240472029373844035694575272524401301329985725154721920
def adaptiveNumericSpans1546_2 : List AdaptiveNumericSpan := [adaptiveNumericSpans1546_2Chunk0].flatten
def adaptiveSpanEven1546_2 := adaptiveSpanTreeOfSpans (coreEvenSpans 773 0 adaptiveNumericSpans1546_2)
def adaptiveSpanWhole1546_2 := adaptiveSpanTreeOfSpans (coreWholeSpans 0 adaptiveNumericSpans1546_2)
theorem adaptiveSpanNumericCheck1546_2 : coreNumericSpansCheck 1509 6 720 1001 adaptiveNumericSpans1546_2 adaptiveRows1546 = true := by decide +kernel
theorem adaptiveSpanEvenCache1546_2 : adaptiveSpanEven1546_2.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain1546_2 : adaptiveSpanEven1546_2.domainCheck 773 = true := by decide +kernel
theorem adaptiveSpanEvenEntries1546_2 : adaptiveSpanEven1546_2.spans = coreEvenSpans 773 0 adaptiveNumericSpans1546_2 := by decide +kernel
theorem adaptiveSpanWholeCache1546_2 : adaptiveSpanWhole1546_2.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain1546_2 : adaptiveSpanWhole1546_2.domainCheck 773 = true := by decide +kernel
theorem adaptiveSpanWholeEntries1546_2 : adaptiveSpanWhole1546_2.spans = coreWholeSpans 0 adaptiveNumericSpans1546_2 := by decide +kernel
def adaptiveNumericSpans1546_3Chunk0 : List AdaptiveNumericSpan := adaptivePackedNumericSpans 11 19119735375777170512439038712518105878979291120282894650360498838053485049665858705053394450464972001359521517656768229908922529188049620348861431329974824308114629516229085201484341481610359028922303013362299084685556212625725366989437181141581621633557776834956434686530778539713409046699211168770730513912435983031701923168320
def adaptiveNumericSpans1546_3 : List AdaptiveNumericSpan := [adaptiveNumericSpans1546_3Chunk0].flatten
def adaptiveSpanEven1546_3 := adaptiveSpanTreeOfSpans (coreEvenSpans 773 0 adaptiveNumericSpans1546_3)
def adaptiveSpanWhole1546_3 := adaptiveSpanTreeOfSpans (coreWholeSpans 0 adaptiveNumericSpans1546_3)
theorem adaptiveSpanNumericCheck1546_3 : coreNumericSpansCheck 1509 6 120 143 adaptiveNumericSpans1546_3 adaptiveRows1546 = true := by decide +kernel
theorem adaptiveSpanEvenCache1546_3 : adaptiveSpanEven1546_3.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain1546_3 : adaptiveSpanEven1546_3.domainCheck 773 = true := by decide +kernel
theorem adaptiveSpanEvenEntries1546_3 : adaptiveSpanEven1546_3.spans = coreEvenSpans 773 0 adaptiveNumericSpans1546_3 := by decide +kernel
theorem adaptiveSpanWholeCache1546_3 : adaptiveSpanWhole1546_3.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain1546_3 : adaptiveSpanWhole1546_3.domainCheck 773 = true := by decide +kernel
theorem adaptiveSpanWholeEntries1546_3 : adaptiveSpanWhole1546_3.spans = coreWholeSpans 0 adaptiveNumericSpans1546_3 := by decide +kernel
def adaptiveNumericSpans1546_4Chunk0 : List AdaptiveNumericSpan := adaptivePackedNumericSpans 15 49371934343154551947034084862082096560997583451978050600313253286517790062754104457828903623038878426863343568484787707424446808428654484884475249311157865930886818325394358765949803293978507845482988096939281393308292660441143177155144413586158002753150520897256522633412121974719161521998078383524877458494581925060600819060091905407192620757126508712758872354880372495117647263329455969313016007932142093648340685766778975528719152414589926244416
def adaptiveNumericSpans1546_4 : List AdaptiveNumericSpan := [adaptiveNumericSpans1546_4Chunk0].flatten
def adaptiveSpanEven1546_4 := adaptiveSpanTreeOfSpans (coreEvenSpans 773 0 adaptiveNumericSpans1546_4)
def adaptiveSpanWhole1546_4 := adaptiveSpanTreeOfSpans (coreWholeSpans 0 adaptiveNumericSpans1546_4)
theorem adaptiveSpanNumericCheck1546_4 : coreNumericSpansCheck 1509 6 192 221 adaptiveNumericSpans1546_4 adaptiveRows1546 = true := by decide +kernel
theorem adaptiveSpanEvenCache1546_4 : adaptiveSpanEven1546_4.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain1546_4 : adaptiveSpanEven1546_4.domainCheck 773 = true := by decide +kernel
theorem adaptiveSpanEvenEntries1546_4 : adaptiveSpanEven1546_4.spans = coreEvenSpans 773 0 adaptiveNumericSpans1546_4 := by decide +kernel
theorem adaptiveSpanWholeCache1546_4 : adaptiveSpanWhole1546_4.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain1546_4 : adaptiveSpanWhole1546_4.domainCheck 773 = true := by decide +kernel
theorem adaptiveSpanWholeEntries1546_4 : adaptiveSpanWhole1546_4.spans = coreWholeSpans 0 adaptiveNumericSpans1546_4 := by decide +kernel
def adaptiveNumericSpans1546_5Chunk0 : List AdaptiveNumericSpan := adaptivePackedNumericSpans 16 62586362204528600694261615781022542944919619499713661707119764475050985394439028707403558895810592735281077438240742837814849376448915250762021084518955997567587208777436722065790545254426489004766688753457126213882488442300371997151418040386328089575531993946380064075174946248017706582668757785526252770064523423093384108036359271423871696158386381557589650028819599135468438679323465845698298241210362578227652650669505907804109102643153183887276183046185178652921581489094720
def adaptiveNumericSpans1546_5 : List AdaptiveNumericSpan := [adaptiveNumericSpans1546_5Chunk0].flatten
def adaptiveSpanEven1546_5 := adaptiveSpanTreeOfSpans (coreEvenSpans 773 0 adaptiveNumericSpans1546_5)
def adaptiveSpanWhole1546_5 := adaptiveSpanTreeOfSpans (coreWholeSpans 0 adaptiveNumericSpans1546_5)
theorem adaptiveSpanNumericCheck1546_5 : coreNumericSpansCheck 1509 6 288 323 adaptiveNumericSpans1546_5 adaptiveRows1546 = true := by decide +kernel
theorem adaptiveSpanEvenCache1546_5 : adaptiveSpanEven1546_5.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain1546_5 : adaptiveSpanEven1546_5.domainCheck 773 = true := by decide +kernel
theorem adaptiveSpanEvenEntries1546_5 : adaptiveSpanEven1546_5.spans = coreEvenSpans 773 0 adaptiveNumericSpans1546_5 := by decide +kernel
theorem adaptiveSpanWholeCache1546_5 : adaptiveSpanWhole1546_5.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain1546_5 : adaptiveSpanWhole1546_5.domainCheck 773 = true := by decide +kernel
theorem adaptiveSpanWholeEntries1546_5 : adaptiveSpanWhole1546_5.spans = coreWholeSpans 0 adaptiveNumericSpans1546_5 := by decide +kernel
end Erdos883Verified
