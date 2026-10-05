import Erdos883AdaptiveSpan15537Level4TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength15537_4 : adaptiveNumericSpans15537_4.length = 402 := by decide +kernel
theorem adaptiveSpanEvenCache15537_4 : adaptiveSpanEven15537_4.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain15537_4 : adaptiveSpanEven15537_4.domainCheck 7769 = true := by decide +kernel
theorem adaptiveSpanEvenEntries15537_4 : adaptiveSpanEven15537_4.spans = coreEvenSpans 7769 0 adaptiveNumericSpans15537_4 := by
  decide +kernel
theorem adaptiveSpanWholeCache15537_4 : adaptiveSpanWhole15537_4.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain15537_4 : adaptiveSpanWhole15537_4.domainCheck 7769 = true := by decide +kernel
theorem adaptiveSpanWholeEntries15537_4 : adaptiveSpanWhole15537_4.spans = coreWholeSpans 0 adaptiveNumericSpans15537_4 := by
  decide +kernel
end Erdos883Verified
