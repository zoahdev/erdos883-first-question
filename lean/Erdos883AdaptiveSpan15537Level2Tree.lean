import Erdos883AdaptiveSpan15537Level2TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength15537_2 : adaptiveNumericSpans15537_2.length = 402 := by decide +kernel
theorem adaptiveSpanEvenCache15537_2 : adaptiveSpanEven15537_2.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain15537_2 : adaptiveSpanEven15537_2.domainCheck 7769 = true := by decide +kernel
theorem adaptiveSpanEvenEntries15537_2 : adaptiveSpanEven15537_2.spans = coreEvenSpans 7769 0 adaptiveNumericSpans15537_2 := by
  decide +kernel
theorem adaptiveSpanWholeCache15537_2 : adaptiveSpanWhole15537_2.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain15537_2 : adaptiveSpanWhole15537_2.domainCheck 7769 = true := by decide +kernel
theorem adaptiveSpanWholeEntries15537_2 : adaptiveSpanWhole15537_2.spans = coreWholeSpans 0 adaptiveNumericSpans15537_2 := by
  decide +kernel
end Erdos883Verified
