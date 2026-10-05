import Erdos883AdaptiveSpan20682Level2TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength20682_2 : adaptiveNumericSpans20682_2.length = 430 := by decide +kernel
theorem adaptiveSpanEvenCache20682_2 : adaptiveSpanEven20682_2.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain20682_2 : adaptiveSpanEven20682_2.domainCheck 10341 = true := by decide +kernel
theorem adaptiveSpanEvenEntries20682_2 : adaptiveSpanEven20682_2.spans = coreEvenSpans 10341 0 adaptiveNumericSpans20682_2 := by
  decide +kernel
theorem adaptiveSpanWholeCache20682_2 : adaptiveSpanWhole20682_2.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain20682_2 : adaptiveSpanWhole20682_2.domainCheck 10341 = true := by decide +kernel
theorem adaptiveSpanWholeEntries20682_2 : adaptiveSpanWhole20682_2.spans = coreWholeSpans 0 adaptiveNumericSpans20682_2 := by
  decide +kernel
end Erdos883Verified
