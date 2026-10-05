import Erdos883AdaptiveSpan15537Level3TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength15537_3 : adaptiveNumericSpans15537_3.length = 402 := by decide +kernel
theorem adaptiveSpanEvenCache15537_3 : adaptiveSpanEven15537_3.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain15537_3 : adaptiveSpanEven15537_3.domainCheck 7769 = true := by decide +kernel
theorem adaptiveSpanEvenEntries15537_3 : adaptiveSpanEven15537_3.spans = coreEvenSpans 7769 0 adaptiveNumericSpans15537_3 := by
  decide +kernel
theorem adaptiveSpanWholeCache15537_3 : adaptiveSpanWhole15537_3.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain15537_3 : adaptiveSpanWhole15537_3.domainCheck 7769 = true := by decide +kernel
theorem adaptiveSpanWholeEntries15537_3 : adaptiveSpanWhole15537_3.spans = coreWholeSpans 0 adaptiveNumericSpans15537_3 := by
  decide +kernel
end Erdos883Verified
