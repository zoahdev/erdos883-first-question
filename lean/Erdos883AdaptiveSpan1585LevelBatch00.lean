import Erdos883AdaptiveCertificate1585Data
import Erdos883AdaptiveSpanCompactCore
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
def adaptiveNumericSpans1585_0Chunk0 : List AdaptiveNumericSpan := adaptivePackedNumericSpans 10 15460903919774965648062926432701699705740401539413765731461177288575467413292584727799191256037078486372017187422656069059599555623000057231820101813554575078939670365613475819846527142198821180145533938260988308441756884954853398899296975918920056126577311390193382320198776749892523985327404089408
def adaptiveNumericSpans1585_0 : List AdaptiveNumericSpan := [adaptiveNumericSpans1585_0Chunk0].flatten
def adaptiveSpanEven1585_0 := adaptiveSpanTreeOfSpans (coreEvenSpans 793 0 adaptiveNumericSpans1585_0)
def adaptiveSpanWhole1585_0 := adaptiveSpanTreeOfSpans (coreWholeSpans 0 adaptiveNumericSpans1585_0)
theorem adaptiveSpanNumericCheck1585_0 : coreNumericSpansCheck 1547 6 480 1155 adaptiveNumericSpans1585_0 adaptiveRows1585 = true := by decide +kernel
theorem adaptiveSpanEvenCache1585_0 : adaptiveSpanEven1585_0.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain1585_0 : adaptiveSpanEven1585_0.domainCheck 793 = true := by decide +kernel
theorem adaptiveSpanEvenEntries1585_0 : adaptiveSpanEven1585_0.spans = coreEvenSpans 793 0 adaptiveNumericSpans1585_0 := by decide +kernel
theorem adaptiveSpanWholeCache1585_0 : adaptiveSpanWhole1585_0.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain1585_0 : adaptiveSpanWhole1585_0.domainCheck 793 = true := by decide +kernel
theorem adaptiveSpanWholeEntries1585_0 : adaptiveSpanWhole1585_0.spans = coreWholeSpans 0 adaptiveNumericSpans1585_0 := by decide +kernel
def adaptiveNumericSpans1585_1Chunk0 : List AdaptiveNumericSpan := adaptivePackedNumericSpans 7 7589902240016328976528471211189468318859543857356065323849533666774034212171588134569425998080905717577208250518667322722111929232204319752643115388469016830647444395590402599109943944382528199450675459915904
def adaptiveNumericSpans1585_1 : List AdaptiveNumericSpan := [adaptiveNumericSpans1585_1Chunk0].flatten
def adaptiveSpanEven1585_1 := adaptiveSpanTreeOfSpans (coreEvenSpans 793 0 adaptiveNumericSpans1585_1)
def adaptiveSpanWhole1585_1 := adaptiveSpanTreeOfSpans (coreWholeSpans 0 adaptiveNumericSpans1585_1)
theorem adaptiveSpanNumericCheck1585_1 : coreNumericSpansCheck 1547 6 240 385 adaptiveNumericSpans1585_1 adaptiveRows1585 = true := by decide +kernel
theorem adaptiveSpanEvenCache1585_1 : adaptiveSpanEven1585_1.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain1585_1 : adaptiveSpanEven1585_1.domainCheck 793 = true := by decide +kernel
theorem adaptiveSpanEvenEntries1585_1 : adaptiveSpanEven1585_1.spans = coreEvenSpans 793 0 adaptiveNumericSpans1585_1 := by decide +kernel
theorem adaptiveSpanWholeCache1585_1 : adaptiveSpanWhole1585_1.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain1585_1 : adaptiveSpanWhole1585_1.domainCheck 793 = true := by decide +kernel
theorem adaptiveSpanWholeEntries1585_1 : adaptiveSpanWhole1585_1.spans = coreWholeSpans 0 adaptiveNumericSpans1585_1 := by decide +kernel
def adaptiveNumericSpans1585_2Chunk0 : List AdaptiveNumericSpan := adaptivePackedNumericSpans 9 12196502661688769086081567783204819005396325337430912251520977681210906562026785474576382074658011890921737836497538879827280688039071523017778053763694510625522776658786822753317721490453080719926333961145540465972357751976820186695227984303355350920950030304689520768
def adaptiveNumericSpans1585_2 : List AdaptiveNumericSpan := [adaptiveNumericSpans1585_2Chunk0].flatten
def adaptiveSpanEven1585_2 := adaptiveSpanTreeOfSpans (coreEvenSpans 793 0 adaptiveNumericSpans1585_2)
def adaptiveSpanWhole1585_2 := adaptiveSpanTreeOfSpans (coreWholeSpans 0 adaptiveNumericSpans1585_2)
theorem adaptiveSpanNumericCheck1585_2 : coreNumericSpansCheck 1547 6 720 1001 adaptiveNumericSpans1585_2 adaptiveRows1585 = true := by decide +kernel
theorem adaptiveSpanEvenCache1585_2 : adaptiveSpanEven1585_2.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain1585_2 : adaptiveSpanEven1585_2.domainCheck 793 = true := by decide +kernel
theorem adaptiveSpanEvenEntries1585_2 : adaptiveSpanEven1585_2.spans = coreEvenSpans 793 0 adaptiveNumericSpans1585_2 := by decide +kernel
theorem adaptiveSpanWholeCache1585_2 : adaptiveSpanWhole1585_2.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain1585_2 : adaptiveSpanWhole1585_2.domainCheck 793 = true := by decide +kernel
theorem adaptiveSpanWholeEntries1585_2 : adaptiveSpanWhole1585_2.spans = coreWholeSpans 0 adaptiveNumericSpans1585_2 := by decide +kernel
def adaptiveNumericSpans1585_3Chunk0 : List AdaptiveNumericSpan := adaptivePackedNumericSpans 10 15460903919774965648062926432701699705740401539413765731461177288575467413292584727799191256162489956533633950574252722318420003989076045478858413774393605639420154741433365354095614743388262633639566700263374768249605974505309547481483071297166424489293139160975450161210972023869018291844994302080
def adaptiveNumericSpans1585_3 : List AdaptiveNumericSpan := [adaptiveNumericSpans1585_3Chunk0].flatten
def adaptiveSpanEven1585_3 := adaptiveSpanTreeOfSpans (coreEvenSpans 793 0 adaptiveNumericSpans1585_3)
def adaptiveSpanWhole1585_3 := adaptiveSpanTreeOfSpans (coreWholeSpans 0 adaptiveNumericSpans1585_3)
theorem adaptiveSpanNumericCheck1585_3 : coreNumericSpansCheck 1547 6 120 143 adaptiveNumericSpans1585_3 adaptiveRows1585 = true := by decide +kernel
theorem adaptiveSpanEvenCache1585_3 : adaptiveSpanEven1585_3.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain1585_3 : adaptiveSpanEven1585_3.domainCheck 793 = true := by decide +kernel
theorem adaptiveSpanEvenEntries1585_3 : adaptiveSpanEven1585_3.spans = coreEvenSpans 793 0 adaptiveNumericSpans1585_3 := by decide +kernel
theorem adaptiveSpanWholeCache1585_3 : adaptiveSpanWhole1585_3.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain1585_3 : adaptiveSpanWhole1585_3.domainCheck 793 = true := by decide +kernel
theorem adaptiveSpanWholeEntries1585_3 : adaptiveSpanWhole1585_3.spans = coreWholeSpans 0 adaptiveNumericSpans1585_3 := by decide +kernel
def adaptiveNumericSpans1585_4Chunk0 : List AdaptiveNumericSpan := adaptivePackedNumericSpans 13 31494417511232480091566335111834970794563678606328443690500400366802957325926575932007876566579232980431350407293719375312494125896879179075875314659426130008381500747136111518958155430626604347582436286319807648319223859221442181168623989814825407940769916146374254910967017648048030144451513258826952479293203379372063691714932422667312065776952516055880169314786569825814193294096203840
def adaptiveNumericSpans1585_4 : List AdaptiveNumericSpan := [adaptiveNumericSpans1585_4Chunk0].flatten
def adaptiveSpanEven1585_4 := adaptiveSpanTreeOfSpans (coreEvenSpans 793 0 adaptiveNumericSpans1585_4)
def adaptiveSpanWhole1585_4 := adaptiveSpanTreeOfSpans (coreWholeSpans 0 adaptiveNumericSpans1585_4)
theorem adaptiveSpanNumericCheck1585_4 : coreNumericSpansCheck 1547 6 192 221 adaptiveNumericSpans1585_4 adaptiveRows1585 = true := by decide +kernel
theorem adaptiveSpanEvenCache1585_4 : adaptiveSpanEven1585_4.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain1585_4 : adaptiveSpanEven1585_4.domainCheck 793 = true := by decide +kernel
theorem adaptiveSpanEvenEntries1585_4 : adaptiveSpanEven1585_4.spans = coreEvenSpans 793 0 adaptiveNumericSpans1585_4 := by decide +kernel
theorem adaptiveSpanWholeCache1585_4 : adaptiveSpanWhole1585_4.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain1585_4 : adaptiveSpanWhole1585_4.domainCheck 793 = true := by decide +kernel
theorem adaptiveSpanWholeEntries1585_4 : adaptiveSpanWhole1585_4.spans = coreWholeSpans 0 adaptiveNumericSpans1585_4 := by decide +kernel
def adaptiveNumericSpans1585_5Chunk0 : List AdaptiveNumericSpan := adaptivePackedNumericSpans 17 81326455778798270754020496423856356943664149076642684902196773344485958950107347565899524640111006363027690088334758896294752846388601811569231525201059205468149115896679508829359336071554017571947635455294606075277368392576191120883067639681757639412692431659042505145567112569180890452998572523101452428103157307134716986646055246301598846597952714195826742473419819102178810714790464554470345046250661016419290540001319864122190953467465889964236880571575582605407893371910470289352216010029254959100330048
def adaptiveNumericSpans1585_5 : List AdaptiveNumericSpan := [adaptiveNumericSpans1585_5Chunk0].flatten
def adaptiveSpanEven1585_5 := adaptiveSpanTreeOfSpans (coreEvenSpans 793 0 adaptiveNumericSpans1585_5)
def adaptiveSpanWhole1585_5 := adaptiveSpanTreeOfSpans (coreWholeSpans 0 adaptiveNumericSpans1585_5)
theorem adaptiveSpanNumericCheck1585_5 : coreNumericSpansCheck 1547 6 288 323 adaptiveNumericSpans1585_5 adaptiveRows1585 = true := by decide +kernel
theorem adaptiveSpanEvenCache1585_5 : adaptiveSpanEven1585_5.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain1585_5 : adaptiveSpanEven1585_5.domainCheck 793 = true := by decide +kernel
theorem adaptiveSpanEvenEntries1585_5 : adaptiveSpanEven1585_5.spans = coreEvenSpans 793 0 adaptiveNumericSpans1585_5 := by decide +kernel
theorem adaptiveSpanWholeCache1585_5 : adaptiveSpanWhole1585_5.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain1585_5 : adaptiveSpanWhole1585_5.domainCheck 793 = true := by decide +kernel
theorem adaptiveSpanWholeEntries1585_5 : adaptiveSpanWhole1585_5.spans = coreWholeSpans 0 adaptiveNumericSpans1585_5 := by decide +kernel
end Erdos883Verified
