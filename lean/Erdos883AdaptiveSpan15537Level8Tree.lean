import Erdos883AdaptiveSpan15537Level8TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength15537_8 : adaptiveNumericSpans15537_8.length = 402 := by decide +kernel
theorem adaptiveSpanEvenCache15537_8 : adaptiveSpanEven15537_8.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain15537_8 : adaptiveSpanEven15537_8.domainCheck 7769 = true := by decide +kernel
theorem adaptiveSpanEvenEntries15537_8 : adaptiveSpanEven15537_8.spans = coreEvenSpans 7769 0 adaptiveNumericSpans15537_8 := by
  decide +kernel
theorem adaptiveSpanWholeCache15537_8 : adaptiveSpanWhole15537_8.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain15537_8 : adaptiveSpanWhole15537_8.domainCheck 7769 = true := by decide +kernel
theorem adaptiveSpanWholeEntries15537_8 : adaptiveSpanWhole15537_8.spans = coreWholeSpans 0 adaptiveNumericSpans15537_8 := by
  decide +kernel
end Erdos883Verified
